-- Prove2me | Theorems.Thm_FracTruthSched_padding_sequence_exists
-- name    : FracTruthSched.padding_sequence_exists
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:21:44.819435+00:00
-- url     : https://prove2.me/theorems/cd8bab61-7693-41bd-9281-d17ca0af1b21
-- title:
--   Appendix A.1 — construction of the padded mechanisms and Claims 2–7
-- statement:
--   Let $n\ge1$, $\ell\ge2$, and let $(R_m)$ be a feasible truthful fractional mechanism family. Suppose $\rho$ is any ratio bound for the family against the integral optimum, in the sense of equation (3). Then the construction of Appendix A.1 yields a sequence of padded mechanisms on $MC_\ell$ satisfying the properties recorded in `PaddingSequence`: exact feasibility, truthfulness and within-class symmetry, the load bound, and the vanishing-error estimates for eligibility, unique zeros and zero-type irrelevance.
--
--   The construction enumerates the positive rationals, forms the finite zero-type list $T_K$, adds between $K$ and $2K$ reservoir tasks of every listed type on every pair of machines, adds a self-loop of value $1/K$, applies $R_m$, symmetrizes over parallel-task permutations, slices to the core tasks, and averages over reservoir-count vectors. In the Lean indexing convention, paper stage $K$ is stage $K-1$.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Appendix A.1, pp.23–26, Claims 2–7; symmetrization is Claim 1, p.24.

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_makespan
import Definitions.Def_FracTruthSched_opt
import Definitions.Def_FracTruthSched_PaddingSequence

set_option autoImplicit false

/-- **Construction of the padded mechanisms** (Anastasiadis et al., arXiv:2611.06642v1,
Appendix A.1, pp.23–26, Claims 2–7). For every `ℓ ≥ 2` and every ratio bound `ρ` for the original
family, the explicit padding, symmetrization, slicing and reservoir-count averaging construction
produces a `PaddingSequence`. -/
theorem FracTruthSched.padding_sequence_exists {n : ℕ} [NeZero n]
    (R : (m : ℕ) → FracMech n (Fin m))
    (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (htruth : ∀ m, IsTruthfulOn Nonneg (R m))
    (ρ : ℝ) (hρ : ∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
      makespan (R m) t ≤ ρ * opt t) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    Nonempty (PaddingSequence R ρ ℓ) := by sorry
