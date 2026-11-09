-- Prove2me | Theorems.Thm_GoodQLTC_theorem_6_1
-- name    : GoodQLTC.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:53:18.417478+00:00
-- url     : https://prove2.me/theorems/31cc69fe-250a-4c42-b147-3c9d97ca5384
-- title:
--   Theorem 6.1: local filling from product expansion
-- statement:
--   Fix $0<\rho\le1$, $\tau\ge1$; let $X$ be regular with degrees $2\le n_1\le\dots\le n_t$, $n_t/n_1\le\tau$, and $\mathcal F$ an $\mathbb F_{2^s}$-cosheaf with compatible base codes. Suppose that for every $f\in X$ and nonempty $I\subseteq\mathrm{codir}(f)$ the family $\{C_{f,i}\}_{i\in I}$ is universally $\rho$-product-expanding. Then for every extension $E/F$, every finite-dimensional $E$-space $R$, all integers $0\le\ell\le j<t$, every $v\in X(\ell)$ and every $z\in C^{j-\ell}_{v,E}(R)$,
--   $$
--   |\delta_{v,E}z|_b\ \ge\ n_1\,\kappa_{t-\ell,\,j-\ell}\ \min_{y\in C^{j-\ell-1}_{v,E}(R)}|z+\delta_{v,E}y|_b .
--   $$
--
--   **Formalization Note** For $j=\ell$ the space $C^{-1}_{v,E}(R)$ is $0$, and the minimum is $|z|_b$.
--
--   Differences from the source:
--   - generalization: universal product expansion over every field extension E/F → the hypothesis quantifies over extensions E in one universe u (a parameter of the theorem); reason: Lean has no type of all fields; the paper's hypothesis (all extensions) implies the one-universe hypothesis, so the statement specializes to the source's
--   - encoding: dist(x, U) = min_{u∈U} |x − u| in an inequality → existence of a nearest u ∈ U satisfying the inequality; reason: the minimum over a finite nonempty set is attained; same instances
--   - encoding: choose bases of all stalks → stalks are coordinate spaces F^{d(f)} (a cosheaf with chosen bases); reason: a cosheaf with a choice of stalk bases is exactly this data; (4.5) depends only on the matrices in those bases
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Theorem 6.1, p.21 (PDF p.24); κ from (6.1)

import Mathlib
import Definitions.Def_GoodQLTC_IsCubicalComplex
import Definitions.Def_GoodQLTC_IsRegular
import Definitions.Def_GoodQLTC_BaseCodeData
import Definitions.Def_GoodQLTC_IsProductExpanding
import Definitions.Def_GoodQLTC_cobdMat
import Definitions.Def_GoodQLTC_localCobd
import Definitions.Def_GoodQLTC_kappa

namespace GoodQLTC

universe u v

/-- **Theorem 6.1** (local filling), Gay–Jeronimo, arXiv:2609.20780 (held version), p.21: suppose
that, for every `f ∈ X` and nonempty `I ⊆ codir(f)`, the family `{C_{f,i}}_{i∈I}` is universally
`ρ`-product-expanding. For every extension `E/F`, every finite-dimensional `E`-space `R`, all
integers `0 ≤ ℓ ≤ j < t`, every `v ∈ X(ℓ)`, and every `z ∈ C^{j−ℓ}_{v,E}(R)`,
`|δ_{v,E} z|_b ≥ n_1 κ_{t−ℓ, j−ℓ} min_{y ∈ C^{j−ℓ−1}_{v,E}(R)} |z + δ_{v,E} y|_b`.

**Formalization Note.** Standing assumptions of §6 (p.21): `0 < ρ ≤ 1`, `τ ≥ 1`, `n_t/n_1 ≤ τ`,
`X` regular with degrees `2 ≤ n_1 ≤ ⋯ ≤ n_t`, `F` a cosheaf over `F = F_{2^s}` with compatible
base codes `D`. Local cochains are indexed by absolute dimension (`C^{j−ℓ}_v` has faces of
dimension `j` above `v`). The minimum over `y` is attained, so it is stated as an existence; for
`j = ℓ` the space `C^{−1}_v` is `0` and the term `δ_{v,E} y` is omitted. -/
theorem theorem_6_1 {t : ℕ} {X : Type} [PartialOrder X] [Fintype X]
    {φ : X → Fin t → Option Bool} {n : Fin t → ℕ} (hn : ∀ i, 2 ≤ n i) (hmono : Monotone n)
    (hX : IsCubicalComplex t φ) (hreg : IsRegular φ n)
    {F : Type} [Field F] [Fintype F] {s : ℕ} (hs : 1 ≤ s) (hF : Fintype.card F = 2 ^ s)
    (Fs : Cosheaf X F) {m : Fin t → Bool → ℕ} (hm : ∀ i b, 0 < m i b ∧ m i b < n i)
    (D : BaseCodeData φ Fs m) (hD : IsCompatible D)
    (ρ τ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hτ : 1 ≤ τ) (ht : 1 ≤ t)
    (hratio : (n ⟨t - 1, by omega⟩ : ℝ) / (n ⟨0, by omega⟩ : ℝ) ≤ τ)
    (hPE : ∀ (f : X) (I : Finset (Fin t)), I.Nonempty → I ⊆ codir φ f →
      IsUnivProductExpanding.{u} ρ (fun i : I => localCode D f i.1))
    (E : Type u) [Field E] [Algebra F E] (R : Type v) [AddCommGroup R] [Module E R]
    [FiniteDimensional E R] (ℓ j : ℕ) (hℓj : ℓ ≤ j) (hjt : j < t) (w : X) (hw : fdim φ w = ℓ)
    (z : LocalCochain φ Fs w j R) :
    ∃ y : LocalCochain φ Fs w (j - 1) R,
      (n ⟨0, by omega⟩ : ℝ) * kappa ρ τ (t - ℓ) (j - ℓ) *
          (blockWeight (z + if ℓ < j then localCobd φ Fs E R w (j - 1) j y else 0) : ℝ) ≤
        (blockWeight (localCobd φ Fs E R w j (j + 1) z) : ℝ) := by sorry

end GoodQLTC
