-- Prove2me | Theorems.Thm_GPSAnalysis_Core_liminf_mesh_size_eq_zero
-- name    : GPSAnalysis.Core.liminf_mesh_size_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T07:45:58.87263+00:00
-- url     : https://prove2.me/theorems/9fa1cc41-1017-42a9-9d29-d1e9cfd1f5bc
-- title:
--   Proposition 3.4 — $\liminf_{k\to\infty}\Delta_k=0$
-- statement:
--   Consider a GPS run satisfying A1 ($f_\Omega(x_0)<\infty$) and A3 (all iterates lie in a compact set). Then the mesh size parameters satisfy
--
--   $$\liminf_{k\to+\infty}\Delta_k=0 .$$
--
--   The statement depends on the rationality of $\tau$ and on the directions being integer combinations of the columns of one nonsingular matrix: these make all iterates lie on one translated lattice. It guarantees that the algorithm detects infinitely many mesh local optimizers on arbitrarily fine meshes.
--
--   **Formalization Note** The limit inferior is taken in the extended reals `EReal`, so it cannot take a default value.
-- source:
--   Audet, Dennis, Analysis of Generalized Pattern Searches, SIAM J. Optim. 13 (2003), p. 896, Proposition 3.4

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh
import Definitions.Def_GPSAnalysis_Core_Run

open Filter

namespace GPSAnalysis.Core

/-- Proposition 3.4 (Audet–Dennis 2003, p. 896). Under A1 and A3,
`liminf_{k → ∞} Δ_k = 0` (the limit inferior is taken in `EReal`). -/
theorem liminf_mesh_size_eq_zero {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hA1 : AssumptionA1 R) (hA3 : AssumptionA3 R) :
    Filter.liminf (fun k => ((R.Δ k : ℝ) : EReal)) atTop = 0 := by sorry

end GPSAnalysis.Core
