-- Prove2me | Theorems.Thm_ModFormPIR_theorem_12_2
-- name    : ModFormPIR.theorem_12_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:33.073137+00:00
-- url     : https://prove2.me/theorems/41608544-f5f2-4e3f-9431-0c0875591e10
-- title:
--   Theorem 12.2, p.66 — an expansion supported on $S_d(\vartheta,\nu)\times\mathcal A$
-- statement:
--   Let $q$ be an odd prime, $s\in[2,q]$, $d\ge1$ divisible by $q$, $(\vartheta,\nu)$ feasible, and $\mathcal A\subseteq\mathbb Z_q$ any set of size $s$. Then there is a quadratic-phase delta expansion on $\mathbb Z_q^d$ with support contained in $S_d(\vartheta,\nu)\times\mathcal A$. In particular, this expansion is $(|S_d(\vartheta,\nu)|,s)$-sparse.
--
--   This is the technical core of the paper: its proof shows that a dual witness to nonexistence would yield modular forms for $\Gamma(q)$ with too many zeros at the cusps.
--
--   Differences from the source:
--   - generalization: over ℚ(ζ_q) → over any field of characteristic 0 with any primitive q-th root γ; reason: the linear system has coefficients in ℤ[γ] ≅ ℤ[ζ_q], so a solution over ℚ(ζ_q) maps to any such field; ℚ(ζ_q) is an instance
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Theorem 12.2, p.66 (PDF p.70), with Definition 12.1, p.66

import Mathlib
import Definitions.Def_ModFormPIR_Expansion

set_option autoImplicit false

namespace ModFormPIR

/-- **Theorem 12.2**, p.66. Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
For `q` an odd prime, `s ∈ [2, q]`, `d ≥ 1` with `q ∣ d`, `(ϑ, ν)` feasible, and any `𝒜 ⊆ ℤ_q` of size `s`, a quadratic-phase delta expansion exists with support in
`S_d(ϑ,ν) × 𝒜`, hence `(|S_d(ϑ,ν)|, s)`-sparse.

**Formalization Note.** Over any field of characteristic `0` with any primitive `q`-th root `γ`, which includes `ℚ(ζ_q)`. -/
theorem theorem_12_2 {K : Type*} [Field K] [CharZero K] (q s d : ℕ) [NeZero q] (hq : q.Prime)
    (hodd : Odd q) (hs : 2 ≤ s) (hsq : s ≤ q) (hd : 1 ≤ d) (hqd : q ∣ d) (ϑ ν : ℝ)
    (hf : Feasible q s ϑ ν) (𝒜 : Finset (ZMod q)) (h𝒜 : 𝒜.card = s) (γ : K)
    (hγ : IsPrimitiveRoot γ q) :
    ∃ c : (Fin d → ZMod q) → ZMod q → K, IsDeltaExpansion γ c ∧
      HasSupport c (Sd q s d ϑ ν) (𝒜 : Set (ZMod q)) ∧
      IsSparse c (Sd q s d ϑ ν).ncard s := by sorry

end ModFormPIR
