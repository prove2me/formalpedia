-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_Supplement_lemma_18
-- name    : LogBarrierIPM.Iterations.Supplement.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:24:07.69318+00:00
-- url     : https://prove2.me/theorems/fa012484-6227-4560-bf4e-7f325c28fdd5
-- title:
--   Lemma 18 — uniform specialization (corrected: dual sign)
-- statement:
--   Assume strict primal-dual feasibility over $K$, and fix any Puiseux optimal pair $z^*=(x^*,w^*,s^*,y^*)$. There is a real $t_0>0$ such that, for every $t>t_0$, the real strictly feasible set is nonempty, the evaluated pair is primal-dual optimal, and the common value is
--   $$\nu(t)=c(t)^\top x^*(t)=-b(t)^\top y^*(t).$$
--   The threshold is also beyond the absolute-convergence radii of all data and optimal-solution series. This supplies exactly the admissible specialization thresholds used in Theorem 19; it is uniform in all $t>t_0$.
--
--   Differences from the source:
--   - correction: the displayed dual says maximize bᵀy → minimize bᵀy, equivalently maximize -bᵀy; reason: the gap on pp. 14–15 is cᵀx+bᵀy; Proposition 14 uses bᵀy+ν≥0, and the central-path barrier on p. 4 already has -bᵀy
--   - encoding: specializations are defined for sufficiently large t → the chosen t0 is beyond each absolute-convergence radius; reason: p. 8 defines P(t) only where the series converge; increasing t0 preserves every conclusion of Lemma 18
--   - encoding: relations over the ordered field K → eventual relations between evaluations of the published convergent series; reason: p. 7 identifies order and equality with eventual evaluations; no domain is restricted
--   - encoding: the number ν(t) → the common value c(t)ᵀx*(t) = -b(t)ᵀy*(t); reason: ν = cᵀx* = -bᵀy* in K, and evaluation commutes with these products beyond the convergence radii
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 17, Lemma 18

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_Specialization

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

theorem lemma_18 {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux)
    (hstrict : StrictlyFeasibleK A b c)
    (zstar : PuiseuxSlackPoint n m) (hopt : OptimalPairK A b c zstar) :
    ∃ t0 : ℝ, SpecializationThreshold A b c zstar t0 := by sorry

end LogBarrierIPM.Iterations.Supplement
