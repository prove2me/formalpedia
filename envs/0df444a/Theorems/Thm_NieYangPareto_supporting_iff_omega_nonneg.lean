-- Prove2me | Theorems.Thm_NieYangPareto_supporting_iff_omega_nonneg
-- name    : NieYangPareto.supporting_iff_omega_nonneg
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:24.497763+00:00
-- url     : https://prove2.me/theorems/a9dae73f-4f23-46a4-adba-9d297b1442f2
-- title:
--   §3.2 after (3.2) — a supporting hyperplane through $v$ exists iff $\omega^*\ge0$
-- statement:
--   Let $m\ge1$ and $v\in f(K)$. A **supporting hyperplane through $v$** is given by a nonzero $w\in\mathbb R^m$ with $w^Tu\ge w^Tv$ for all $u\in\mathcal U$. There is one if and only if the optimal value of (3.2) satisfies
--
--   $$
--   \omega^*\ge0 .
--   $$
--
--   This turns a geometric question into the value of a linear program over the cone $\mathscr P_d(K)$.
--
--   Differences from the source:
--   - encoding: disjoint finite label sets ℰ, ℐ → two finite types E, I (`[Finite E] [Finite I]`), each with its own constraint family; reason: separate types encode disjointness; the same instances
--   - reading: "max" in (3.2) → supremum in EReal, so that ω* = ⊥ exactly when (3.2) is infeasible; reason: the page compares optimal values and speaks of infeasibility; a real supremum would return the junk value 0
--   - reading: m unbounded below ("several objective functions") → hypothesis 0 < m; reason: at m = 0 the equality of (3.3) reads 1 = 0 and eᵀw = 1 reads 0 = 1, so the programs are meaningless there
--   - encoding: "a supporting hyperplane through v" → ∃ w ≠ 0 with wᵀv ≤ wᵀu for all u ∈ 𝒰; reason: the definition on p.6; v ∈ U holds because v ∈ f(K)
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, §3.2 after (3.2), p.8; definition of supporting hyperplane through v, p.6

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_MOP_U
import Definitions.Def_NieYangPareto_Programs

namespace NieYangPareto

/-- **A supporting hyperplane through `v` exists iff `ω* ≥ 0`.** Nie–Yang, arXiv:2108.04336v2, §3.2
after (3.2), p.8: for `v ∈ f(K)`, "there is a supporting hyperplane through v if and only if the
optimal value ω* ≥ 0."

"Supporting hyperplane through `v`" is the definition on p.6: `v ∈ 𝒰` (here `v ∈ f(K) ⊆ 𝒰`) and a
nonzero `w` with `wᵀu ≥ wᵀv` for all `u ∈ 𝒰`.

**Formalization Note** `0 < m` is needed: for `m = 0` the constraint `eᵀw = 1` of (3.2) reads
`0 = 1`. -/
theorem supporting_iff_omega_nonneg {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I)
    (hm : 0 < m) (v : Fin m → ℝ) (hv : v ∈ P.obj '' P.K) :
    (∃ w : Fin m → ℝ, w ≠ 0 ∧ ∀ u ∈ P.U, w ⬝ᵥ v ≤ w ⬝ᵥ u) ↔ 0 ≤ P.omegaStar v := by sorry

end NieYangPareto
