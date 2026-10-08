-- Prove2me | Theorems.Thm_KelsoCrawford_FirmOptimal_salary_adjustment_firm_optimal
-- name    : KelsoCrawford.FirmOptimal.salary_adjustment_firm_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:27.195416+00:00
-- url     : https://prove2.me/theorems/3381d960-4e13-4cf3-a99f-cb82e708fd22
-- title:
--   Theorem 4 — without ties, the salary-adjustment process converges to the firm-optimal discrete strict core allocation
-- statement:
--   Consider a discrete market with salary unit $\delta > 0$: finitely many workers and at least one firm, utilities $u^i(j;\cdot)$ strictly increasing and continuous, technologies satisfying (MP) and (NFL), and every firm's demand satisfying (GS) on the permitted salary vectors $\sigma_{ij} + \delta\mathbb{N}$. Suppose the no-ties conditions (NTW) and (NTF) hold. Then for every run of the salary-adjustment process R1–R5:
--
--   1. the run stops: there is a round $T$ in which no rejections are issued;
--   2. at every round $T$ in which it stops, the resulting allocation $(\phi; s_{1\phi(1)}, \dots, s_{m\phi(m)})$ is a discrete strict core allocation, and it is at least as good for every firm as any other discrete strict core allocation $(f; s'_{1f(1)}, \dots, s'_{mf(m)})$:
--   $$y^j(C^j_{f}) - \sum_{i \in C^j_f} s'_{ij} \;\le\; y^j(C^j_\phi) - \sum_{i \in C^j_\phi} s_{ij} \qquad \text{for every firm } j.$$
--
--   This is the money analogue of Gale and Shapley's result that deferred acceptance yields the stable matching most favorable to the proposing side: the process reaches the firms' end of the strict core.
--
--   **Formalization Note** "Converges" is read as: every run stops in finite time, and every stopping round yields the stated allocation. "Any other strict core allocation" means any discrete strict core allocation of the same discrete market. "At least as good for every firm" is a weak profit inequality at every firm. The standing assumptions of p. 1486 are hypotheses; the reservation-salary relation $u^i(j;\sigma_{ij}) = u^i(0;0)$ is not imposed (Section 5 perturbs $\sigma_{ij}$ independently of it). The statement is about all runs, i.e. all tie-breaking rules.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1495, Theorem 4

import Mathlib
import Definitions.Def_KelsoCrawford_FirmOptimal_Model
import Definitions.Def_KelsoCrawford_FirmOptimal_Process
import Definitions.Def_KelsoCrawford_FirmOptimal_NoTies

namespace KelsoCrawford.FirmOptimal

theorem salary_adjustment_firm_optimal
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) (M.gridVectors δ j))
    (hNTW : M.NTW δ) (hNTF : M.NTF δ) :
    ∀ ρ : Run W F, M.IsRun δ ρ →
      (∃ T, ρ.Stopped T) ∧
      ∀ T, ρ.Stopped T →
        M.IsStrictCore (M.grid δ) (ρ.outcome T) ∧
        ∀ A' : Allocation W F, M.IsStrictCore (M.grid δ) A' →
          ∀ j, KelsoCrawford.Process.profit (M.y j) (A'.hired j) A'.sal ≤
            KelsoCrawford.Process.profit (M.y j) ((ρ.outcome T).hired j) (ρ.outcome T).sal := by sorry

end KelsoCrawford.FirmOptimal
