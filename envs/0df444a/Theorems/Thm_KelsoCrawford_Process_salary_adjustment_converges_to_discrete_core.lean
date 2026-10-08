-- Prove2me | Theorems.Thm_KelsoCrawford_Process_salary_adjustment_converges_to_discrete_core
-- name    : KelsoCrawford.Process.salary_adjustment_converges_to_discrete_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:46:40.684384+00:00
-- url     : https://prove2.me/theorems/197e481b-a45e-446e-b9fc-0e697edb1515
-- title:
--   Theorem 1 — the salary-adjustment process R1–R5 converges in finite time to a discrete core allocation
-- statement:
--   Consider a job-matching market with finitely many workers and at least one firm, in which every utility $u^i(j;\cdot)$ is strictly increasing and continuous, and which satisfies (MP), (NFL), and the gross-substitutes condition (GS) for the discrete market with salary unit $\delta > 0$ (salaries $\sigma_{ij} + k\delta$, $k = 0, 1, 2, \dots$). Then:
--
--   1. the salary-adjustment process R1–R5 with unit $\delta$ has at least one run;
--   2. every run, whatever ties firms and workers break and however, reaches a round $T$ in which no rejections are issued; and
--   3. at every such round $T$, the allocation in which each worker accepts the offer he or she holds, at its permitted salary, is a discrete core allocation (D3):
--
--   $$\Big(\exists\, \text{run}\Big) \ \wedge\ \forall\, \rho \text{ run}:\ \Big(\exists T,\ \rho \text{ stops at } T\Big) \wedge \Big(\forall T,\ \rho \text{ stops at } T \Rightarrow \text{outcome}_\rho(T) \in \operatorname{Core}_\delta\Big).$$
--
--   This is Theorem 1 of the paper: "The salary-adjustment process R1–R5 converges in finite time to a discrete core allocation in the discrete market for which it is defined." It shows in particular that every discrete market satisfying these assumptions has a core allocation, which the paper uses in the proof of Theorem 2 (the continuous market).
--
--   **Formalization Note** "Converges in finite time" is read as: every legal run has a round without rejections (R5). "To a discrete core allocation" is stated for every such round, not only the first. Part 1 is included so that parts 2–3 are not vacuous. (GS) is assumed for the discrete market only. The starting salaries $\sigma_{ij}$ are data and the relation $u^i(j;\sigma_{ij}) = u^i(0;0)$ is not assumed, which makes the statement more general. The paper's unit is $1$; a general $\delta > 0$ is the same theorem after rescaling, and later results of the paper let the unit shrink.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1489, Theorem 1

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Process_Process

namespace KelsoCrawford.Process

/-- Theorem 1, p. 1489: the salary-adjustment process R1–R5 converges in finite time to a discrete core allocation in the discrete market for which it is defined. A run exists; every run (every tie-breaking) reaches a round without rejections; and the allocation at every such round is a discrete core allocation. -/
theorem salary_adjustment_converges_to_discrete_core
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, GrossSubstitutesOn (M.y j) (M.gridVectors δ j)) :
    (∃ ρ : Run W F, M.IsRun δ ρ) ∧
      ∀ ρ : Run W F, M.IsRun δ ρ →
        (∃ T : ℕ, ρ.Stopped T) ∧ ∀ T : ℕ, ρ.Stopped T → M.IsCore (M.grid δ) (ρ.outcome T) := by sorry

end KelsoCrawford.Process
