-- Prove2me | Theorems.Thm_GPSAnalysis_Core_exists_convergent_refining
-- name    : GPSAnalysis.Core.exists_convergent_refining
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T07:51:41.443225+00:00
-- url     : https://prove2.me/theorems/3b00223d-f4f4-492a-96a5-fca4e5bd52f6
-- title:
--   Theorem 3.6 — there exists a convergent refining subsequence
-- statement:
--   Consider a GPS run satisfying A1 ($f_\Omega(x_0)<\infty$) and A3 (all iterates lie in a compact set). Then there exists at least one **convergent refining subsequence**: an infinite set of indices $K$ such that every $x_k$, $k\in K$, is a mesh local optimizer,
--
--   $$\lim_{k\in K}\Delta_k=0,\qquad\text{and}\qquad \lim_{k\in K}x_k=\hat x\ \text{ for some }\hat x\in\mathbb R^n .$$
--
--   This is the result that makes the main theorem (Theorem 3.7) non-vacuous: its hypothesis "$\hat x$ is a limit of a refining subsequence" is met by every run satisfying A1 and A3.
--
--   **Formalization Note** The index set $K$ is a strictly increasing map $\mathbb N\to\mathbb N$.
-- source:
--   Audet, Dennis, Analysis of Generalized Pattern Searches, SIAM J. Optim. 13 (2003), p. 896, Theorem 3.6

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh
import Definitions.Def_GPSAnalysis_Core_Run

open Filter Topology

namespace GPSAnalysis.Core

/-- Theorem 3.6 (Audet–Dennis 2003, p. 896). Under A1 and A3 there exists at least one
convergent refining subsequence. -/
theorem exists_convergent_refining {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hA1 : AssumptionA1 R) (hA3 : AssumptionA3 R) :
    ∃ (K : ℕ → ℕ) (xhat : Fin n → ℝ), IsRefiningSubseq R K ∧
      Tendsto (fun i => R.x (K i)) atTop (𝓝 xhat) := by sorry

end GPSAnalysis.Core
