-- Prove2me | Theorems.Thm_GnpColoring_lemma_5_6
-- name    : GnpColoring.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:34:10.079527+00:00
-- url     : https://prove2.me/theorems/4dbd8d09-8a6c-49b4-aee9-52b27f8f5ab6
-- title:
--   Lemma 5.6 — one-level separator comparison
-- statement:
--   Let $0<\eta<\varepsilon\le1/2$. For all sufficiently large $d$, every integer $q\ge d+d^{1/2+\varepsilon}$, every graph $G$ and every vertex set $T$ with $G[T]$ a tree or unicyclic, let $C$ be a separator of $T$ as in Lemma 5.5 (connected, each component $T_i$ of $G[T\setminus C]$ a tree attached to $C$ by one edge at a low-degree vertex). Let $\tau$ be a feasible admissible colouring of $V\setminus T$ and $\nu=\nu_{T,\tau}$. Then:
--
--   1. for every $f$, with $E_0(f)=\mathbb E_\nu[\mathrm{Var}_\nu[f\mid\sigma_C]]$ and $E_v(f)=\mathbb E_\nu[\mathrm{Var}_\nu[f\mid\sigma_{T\setminus\{v\}}]]$,
--   $$\mathrm{Var}_\nu[f]\le K_C\Big(E_0(f)+\sum_{v\in C}E_v(f)\Big),\qquad K_C=3(2k+3)q^k\exp\Big(\frac{4\ell+28r_H}{q}\Big);\tag{5.4}$$
--   2. if $F_i\ge1$ and $\tau_{\mathrm{rel}}(T_i,\xi)\le F_i$ for every feasible $\xi$ on $V\setminus T_i$ agreeing with $\tau$ off $T$, then
--   $$\tau_{\mathrm{rel}}(T,\tau)\le K_C\max\{1,\max_iF_i\}.\tag{5.5}$$
--
--   Applied recursively along the separator hierarchy this bounds the relaxation time inside a block.
--
--   Differences from the source:
--   - encoding: "Let T, C, … be as above" in the regime of Section 5.1 with d large → $\exists d_0\,\forall d\ge d_0\,\forall q\ge d+d^{1/2+\varepsilon}$; reason: Section 5.1, p.43
--   - reading: "a separator C as supplied by Lemma 5.5" → any $C$ with the properties Lemma 5.5 asserts (`IsSeparator`); reason: the stronger reading; it contains the separator built in the proof
--   - encoding: $F_i\ge1$ per child and $K_C\max\{1,\max_iF_i\}$ → one $M\ge1$ bounding every child, conclusion $K_CM$; reason: equivalent: take $M=\max\{1,\max_iF_i\}$; the relaxation inequality is monotone
--   - encoding: $\tau_{\mathrm{rel}}\le X$ → `RelaxBound` with constant $X$; reason: Definition 5.2; all constants are $\ge1$
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Lemma 5.6, Eqs. (5.4)–(5.5), p.46

import Mathlib
import Definitions.Def_GnpColoring_IsTreeOrUnicyclic
import Definitions.Def_GnpColoring_IsSeparator
import Definitions.Def_GnpColoring_separatorConst
import Definitions.Def_GnpColoring_IsAdmissible
import Definitions.Def_GnpColoring_IsFeasible
import Definitions.Def_GnpColoring_RelaxBound
import Definitions.Def_GnpColoring_blocks
import Definitions.Def_GnpColoring_variance
import Definitions.Def_GnpColoring_condVar
import Definitions.Def_GnpColoring_expect
import Definitions.Def_mm_transport
import Definitions.Def_SpinGirth5_heatBath

open scoped Classical
open Finset

namespace GnpColoring

/-- **Lemma 5.6 (one-level separator comparison).** In the regime of Section 5.1 (`0 < η < ε ≤ 1/2`,
`q ≥ d + d^(1/2+ε)`, `d` large), let `G[T]` be a tree or unicyclic, `C` a separator of `T` as in
Lemma 5.5 (connected; every component of `G[T ∖ C]` a tree attached to `C` by exactly one edge
at a low-degree vertex), and `T₁, …, T_m` the components of `G[T ∖ C]`. For every feasible admissible exterior colouring `τ` of `V ∖ T`, with `ν = ν_{T,τ}`:
(5.4) `Var_ν[f] ≤ K_C (E₀(f) + Σ_{v∈C} E_v(f))` for every `f`, where
`K_C = 3(2k + 3) q^k exp((4ℓ + 28 r_H)/q)`, `E₀(f) = E_ν[Var_ν[f | σ_C]]`, `E_v(f) = E_ν[Var_ν[f | σ_{T∖{v}}]]`;
(5.5) if `τ_rel(T_i, ξ) ≤ F_i` (`F_i ≥ 1`) for every feasible `ξ` on `V ∖ T_i` with `ξ_{V∖T} = τ`, then
`τ_rel(T, τ) ≤ K_C max{1, max_i F_i}`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Lemma 5.6, p.46, Eqs. (5.4) and (5.5): "Let T, C, and T1, . . . , Tm be as above. For every
feasible admissible exterior coloring τ ∈ [q]^(V∖T), set ν = ν_{T,τ}. Then, for every real-valued
function f on the proper extensions of τ to T, …"; "as above" (p.45) is "a separator C as supplied
by Lemma 5.5".

**Formalization Note** Regime of Section 5.1, p.43 ("take d sufficiently large depending on these
fixed parameters"); `A, C` do not enter. `C` is any separator with the properties Lemma 5.5
asserts (`IsSeparator`), which includes the one its proof constructs. (5.5) is stated with one bound `M ≥ 1` for all children:
given `F_i`, take `M = max{1, max_i F_i}` (the relaxation inequality is monotone in its constant),
and conversely. The children `T_i` are the blocks of `V ∖ (T ∖ C)`, i.e. the components of
`G[T ∖ C]`. `ν = SpinGirth5.pin µ (V ∖ T) x`. -/
theorem lemma_5_6 :
    ∀ η ε : ℝ, 0 < η → η < ε → ε ≤ 1 / 2 →
    ∃ d₀ : ℝ, ∀ d : ℝ, d₀ ≤ d → ∀ q : ℕ, d + d ^ ((1 : ℝ) / 2 + ε) ≤ (q : ℝ) →
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (T Csep : Finset (Fin n)),
      IsTreeOrUnicyclic G T → IsSeparator G d η T Csep →
      ∀ x : Fin n → Fin q, IsAdmissible G q d η T x →
        (∀ f : (Fin n → Fin q) → ℝ,
          variance (SpinGirth5.pin (MarkovMixing.properColoringDist G q) (univ \ T) x) f ≤
            separatorConst G q d η T Csep *
              (expect (SpinGirth5.pin (MarkovMixing.properColoringDist G q) (univ \ T) x)
                  (condVar (SpinGirth5.pin (MarkovMixing.properColoringDist G q) (univ \ T) x) (T \ Csep) f) +
                ∑ v ∈ Csep, expect (SpinGirth5.pin (MarkovMixing.properColoringDist G q) (univ \ T) x)
                  (condVar (SpinGirth5.pin (MarkovMixing.properColoringDist G q) (univ \ T) x) {v} f))) ∧
        (∀ M : ℝ, 1 ≤ M →
          (∀ Ti ∈ blocks G (univ \ (T \ Csep)), ∀ ξ : Fin n → Fin q,
            IsFeasible G q Ti ξ → (∀ w, w ∉ T → ξ w = x w) → RelaxBound G q Ti ξ M) →
          RelaxBound G q T x (separatorConst G q d η T Csep * M)) := by sorry

end GnpColoring
