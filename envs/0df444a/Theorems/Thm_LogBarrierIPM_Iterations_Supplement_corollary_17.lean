-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_Supplement_corollary_17
-- name    : LogBarrierIPM.Iterations.Supplement.corollary_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:22:54.073885+00:00
-- url     : https://prove2.me/theorems/58aaa63b-8250-4e71-9940-b928185e73ca
-- title:
--   Corollary 17 — monotonicity and unit coordinate increments
-- statement:
--   Under Assumption 13, let $a\le b$ be real tropical levels and let $e$ be the all-ones vector. Then
--   $$C^{\rm trop}(a)\le C^{\rm trop}(b)\le C^{\rm trop}(a)+(b-a)e.$$
--   All inequalities are coordinatewise on all $2N$ finite coordinates. This controls the change of the tropical central point when the proof of Theorem 19 changes its level.
--
--   Differences from the source:
--   - encoding: the point C^trop(λ) of T^{2N}, indexed from 1 → a real vector indexed by Fin ((n+m)+(n+m)), in the order x, w, s, y; reason: under Assumption 13 all coordinates are finite by (20); Theorem 15 asserts that this vector is the barycenter
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 16, Corollary 17

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_TropicalLP

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

theorem corollary_17 {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux)
    (hstrict : StrictlyFeasibleK A b c)
    (a b' : ℝ) (hab : a ≤ b') :
    tropicalPath A b c a ≤ tropicalPath A b c b' ∧
    tropicalPath A b c b' ≤ tropicalPath A b c a + (fun _ => b' - a) := by sorry

end LogBarrierIPM.Iterations.Supplement
