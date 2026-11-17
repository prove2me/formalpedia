-- Prove2me | Theorems.Thm_LinMaxLoad_Supplement_theorem_14
-- name    : LinMaxLoad.Supplement.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:25:00.624207+00:00
-- url     : https://prove2.me/theorems/ad78e675-325e-40b0-baf8-ac6bfa4d8531
-- title:
--   Theorem 14 — $q(S) = \Omega(1)$ iff $S = S + V$ with $\dim V = \ell - O(1)$ and $\pi(S)$ injectively mappable
-- statement:
--   Fix a prime $p$. For a set $S \subseteq \mathbb F_p^u$ of size $n := p^\ell$, $q(S) = \Omega(1)$ if and only if there is a subspace $V \le \mathbb F_p^u$ of dimension $d = \ell - O(1)$ such that
--
--   1. $S = S + V$, and
--   2. there is a linear map $h' : \mathbb F_p^u/V \to \mathbb F_p^{\ell-d}$ with $M(\pi(S), h') = 1$, where $\pi : \mathbb F_p^u \to \mathbb F_p^u/V$ is the coset map $x \mapsto x + V$.
--
--   Precisely, both directions hold with constants depending only on $p$:
--
--   - (⇒) for every $\delta > 0$ there is $D$ such that for all $u, \ell$ and every $S$ of size $p^\ell$ with $q(S) \ge \delta$, a subspace $V$ as above exists with $\ell - D \le d \le \ell$;
--   - (⇐) for every $D$ there is $\delta > 0$ such that for all $u, \ell$, every $S$ of size $p^\ell$ that has such a subspace $V$ with $\ell - D \le d \le \ell$ satisfies $q(S) \ge \delta$.
--
--   This classifies the sets of size a power of $p$ that a random linear map hashes injectively with constant probability.
--
--   Differences from the source:
--   - reading: $q(S) = \Omega(1)$ iff $d = \ell - O(1)$, with $p$ fixed → two implications: $\forall p\,\forall\delta>0\,\exists D\,\forall u,\ell,S$ (⇒) and $\forall p\,\forall D\,\exists\delta>0\,\forall u,\ell,S,V$ (⇐); reason: the paper fixes $p$ (§4, p.13 “For fixed p”; Theorem 2 writes $O_{p,\delta}(1)$); this is the standard meaning of an equivalence of $\Omega(1)$/$O(1)$ conditions
--   - encoding: $d = \ell - O(1)$ → $\ell \le d + D$ and $d \le \ell$; reason: $d \le \ell$ holds automatically when $S = S + V$ and $|S| = p^\ell$, and makes $\ell - d$ an honest difference
--   - encoding: $\mathbb F_p^u/V$, $\pi$, $\pi(S)$, $S + V$, $M$, $q$ → quotient module `(Fin u → ZMod p) ⧸ V`, `V.mkQ`, `S.image V.mkQ`, `cosetSum V S`, `maxLoad`, `injProb`; reason: Lean convention; same instances
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Theorem 14, p.14

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad
import Definitions.Def_LinMaxLoad_cosetSum
import Definitions.Def_LinMaxLoad_Supplement_injProb

namespace LinMaxLoad.Supplement

open LinMaxLoad

open Classical in
/-- **Theorem 14** (p.14) of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `S ⊆ F_p^u` be a set of size `n := p^ℓ`. Then `q(S) = Ω(1)` if and only if there exists
`V ≤ F_p^u` of dimension `d = ℓ − O(1)` such that (1) `S = S + V`, and (2) there exists a linear
map `h′ : F_p^u/V → F_p^{ℓ−d}` such that `M(π(S), h′) = 1`, where `π : F_p^u → F_p^u/V` is the
coset map `x ↦ x + V`.

**Formalization Note** The prime `p` is fixed (§4, p.13: "For fixed p"; Theorem 2, p.4, writes
the bound as `O_{p,δ}(1)`), so the implied constants may depend on `p` but on nothing else. The
equivalence of two asymptotic conditions is stated as two implications: (⇒) for every `δ > 0`
there is `D` such that every `S` of size `p^ℓ` (any `u, ℓ`) with `q(S) ≥ δ` has such a `V`
with `ℓ − D ≤ d ≤ ℓ`; (⇐) for every `D` there is `δ > 0` such that every `S` of size `p^ℓ`
having such a `V` with `ℓ − D ≤ d ≤ ℓ` has `q(S) ≥ δ`. `d ≤ ℓ` holds automatically for
`S = S + V` with `|S| = p^ℓ`; it makes `ℓ − d` an honest difference. `π` is `V.mkQ`, `π(S)` its
image, `S + V` is `cosetSum V S`, `M` is `maxLoad` and `q(S)` is `injProb`. -/
theorem theorem_14 :
    (∀ (p : ℕ) [Fact p.Prime] (δ : ℝ), 0 < δ → ∃ D : ℕ,
      ∀ (u ℓ : ℕ) (S : Finset (Fin u → ZMod p)), S.card = p ^ ℓ → δ ≤ injProb p u S →
        ∃ V : Submodule (ZMod p) (Fin u → ZMod p),
          ℓ ≤ Module.finrank (ZMod p) V + D ∧ Module.finrank (ZMod p) V ≤ ℓ ∧
          cosetSum V S = S ∧
          ∃ h' : ((Fin u → ZMod p) ⧸ V) →ₗ[ZMod p]
              (Fin (ℓ - Module.finrank (ZMod p) V) → ZMod p),
            maxLoad (h' : (Fin u → ZMod p) ⧸ V → Fin (ℓ - Module.finrank (ZMod p) V) → ZMod p)
              (S.image V.mkQ) = 1) ∧
    (∀ (p : ℕ) [Fact p.Prime] (D : ℕ), ∃ δ : ℝ, 0 < δ ∧
      ∀ (u ℓ : ℕ) (S : Finset (Fin u → ZMod p)), S.card = p ^ ℓ →
      ∀ V : Submodule (ZMod p) (Fin u → ZMod p),
        ℓ ≤ Module.finrank (ZMod p) V + D → Module.finrank (ZMod p) V ≤ ℓ →
        cosetSum V S = S →
        (∃ h' : ((Fin u → ZMod p) ⧸ V) →ₗ[ZMod p]
              (Fin (ℓ - Module.finrank (ZMod p) V) → ZMod p),
            maxLoad (h' : (Fin u → ZMod p) ⧸ V → Fin (ℓ - Module.finrank (ZMod p) V) → ZMod p)
              (S.image V.mkQ) = 1) →
        δ ≤ injProb p u S) := by sorry

end LinMaxLoad.Supplement
