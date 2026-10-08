-- Prove2me | Theorems.Thm_MFGPlanning_Penalized_proposition_1
-- name    : MFGPlanning.Penalized.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T20:00:00.132695+00:00
-- url     : https://prove2.me/theorems/0b7572ae-d421-4b29-a68d-0c22f0cac5bc
-- title:
--   Proposition 1 — uniqueness of $M$, and of $U$ normalized by $\sum U^0 = 0$ when $g$ is strictly convex, for the planning scheme (18)
-- statement:
--   Assume the hypotheses of Theorem 1 ((G1), (G3), (G4), (G5), (24), $m_0, m_T \in \mathcal K$, $m_0 > 0$, and $\nu > 0$ or $\nu = 0$ with $m_T > 0$). If $(U^n_{i,j}, M^n_{i,j})$ and $(\widetilde U^n_{i,j}, \widetilde M^n_{i,j})$ are solutions of the planning scheme (18), then
--   $$
--   M^n_{i,j} = \widetilde M^n_{i,j} \quad \text{for all } n = 0, \dots, N_T \text{ and all } (i,j).
--   $$
--   If moreover $q \mapsto g(x_{i,j}, q)$ is strictly convex at every grid point and $\sum_{i,j} U^0_{i,j} = \sum_{i,j}\widetilde U^0_{i,j} = 0$, then
--   $$
--   U^n_{i,j} = \widetilde U^n_{i,j} \quad \text{for all } n = 0, \dots, N_T \text{ and all } (i,j).
--   $$
--
--   The value function of the planning scheme is determined only up to an additive constant, which is why the normalization is needed. This uniqueness turns subsequential convergence into convergence of the whole penalized family in Proposition 4.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §3.1, Proposition 1, p. 12

import Mathlib
import Definitions.Def_MFGPlanning_Penalized_Grid
import Definitions.Def_MFGPlanning_Penalized_Hyp
import Definitions.Def_MFGPlanning_Penalized_Scheme

namespace MFGPlanning.Penalized

/-- Proposition 1, hal-00465404v1, §3.1, p. 12 (PDF 13): under the assumptions of Theorem 1, if
(U, M) and (Ũ, M̃) solve the planning scheme (18), then M^n = M̃^n for all n = 0, …, N_T. If moreover
the numerical Hamiltonian g is strictly convex and Σ_{i,j} U^0_{i,j} = Σ_{i,j} Ũ^0_{i,j} = 0, then
U^n = Ũ^n for all n.
Formalization Note: strict convexity of g is strict convexity of q ↦ g(x_{i,j}, q) at every grid
point. -/
theorem proposition_1 (d : Data) (hG1 : G1 d) (hG3 : G3 d) (hG4 : G4 d) (hG5 : G5 d) (hW : HypW d)
    (hm0 : InK d d.m0) (hmT : InK d d.mT) (hm0pos : ∀ p, 0 < d.m0 p)
    (hνmT : 0 < d.ν ∨ (d.ν = 0 ∧ ∀ p, 0 < d.mT p)) :
    ∀ U M U' M' : Fin (d.NT + 1) → Pt d → ℝ, IsPlanningSol d U M → IsPlanningSol d U' M' →
      M = M' ∧
        ((∀ p, StrictConvexOn ℝ Set.univ (d.g p)) → ∑ p, U 0 p = 0 → ∑ p, U' 0 p = 0 →
          U = U') := by sorry

end MFGPlanning.Penalized
