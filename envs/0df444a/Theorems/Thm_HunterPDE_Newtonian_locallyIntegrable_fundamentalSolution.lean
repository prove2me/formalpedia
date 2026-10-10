-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_locallyIntegrable_fundamentalSolution
-- name    : HunterPDE.Newtonian.locallyIntegrable_fundamentalSolution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T21:24:03.477975+00:00
-- url     : https://prove2.me/theorems/1981662e-f893-4484-bc85-2750135d3971
-- title:
--   Local integrability of the Newtonian fundamental solution
-- statement:
--   For every dimension $n\ge2$, Hunter’s fundamental solution $\Gamma_n$ is locally Lebesgue integrable on $\mathbb R^n$: its norm has finite integral over each compact set. The power singularity in dimensions at least three and the logarithmic singularity in dimension two are both integrable. This is the kernel regularity needed to form Newtonian potentials of continuous compactly supported sources.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed p. 33, Section 2.6.1, assertion following Eq. (2.15), and fundamental solution Eq. (2.12); power integrability criterion Example 1.13.

import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory HunterPDE.Newtonian

theorem HunterPDE.Newtonian.locallyIntegrable_fundamentalSolution (n : ℕ) (hn : 2 ≤ n) :
    LocallyIntegrable (fundamentalSolution n) volume := by sorry
