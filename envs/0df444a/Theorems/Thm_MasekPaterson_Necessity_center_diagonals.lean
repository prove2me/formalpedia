-- Prove2me | Theorems.Thm_MasekPaterson_Necessity_center_diagonals
-- name    : MasekPaterson.Necessity.center_diagonals
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:21:54.030962+00:00
-- url     : https://prove2.me/theorems/60805d10-c228-4dce-9b8a-7e06342e343a
-- title:
--   Lemma 7 — δ_{k,k} = k − μ_k and δ_{k,k+1} = δ_{k+1,k} = 5 + (μ_{k+1} + μ_k)π
-- statement:
--   In the §4.1 example, with $\delta_{i,j} = \delta(\gamma, A^i, B^j)$, for every natural number $k$:
--
--   1. $$\delta_{k,k} = k - \mu_k;$$
--   2. $$\delta_{k,k+1} = \delta_{k+1,k} = 5 + (\mu_{k+1} + \mu_k)\,\pi.$$
--
--   These are the exact values of the edit distances on the main diagonal and on the two adjacent diagonals of the edit matrix. The main diagonal consists of integers, while the adjacent diagonals carry integer multiples of $\pi$ plus $5$.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 30, Lemma 7

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Necessity_editPaths
import Definitions.Def_MasekPaterson_Necessity_example
open MasekPaterson.Shared

namespace MasekPaterson.Necessity

/-- Lemma 7: for all `k`, (a) `δ_{k,k} = k - μ_k` and
(b) `δ_{k,k+1} = δ_{k+1,k} = 5 + (μ_{k+1} + μ_k) π`. -/
theorem center_diagonals (k : ℕ) :
    exDelta k k = (k : ℝ) - (mu k : ℝ) ∧
    (exDelta k (k + 1) = exDelta (k + 1) k ∧
      exDelta (k + 1) k = 5 + ((mu (k + 1) : ℝ) + (mu k : ℝ)) * Real.pi) := by sorry

end MasekPaterson.Necessity
