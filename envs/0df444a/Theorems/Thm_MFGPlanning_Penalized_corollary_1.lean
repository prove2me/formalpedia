-- Prove2me | Theorems.Thm_MFGPlanning_Penalized_corollary_1
-- name    : MFGPlanning.Penalized.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:59:47.290348+00:00
-- url     : https://prove2.me/theorems/121ca638-bbca-4bb8-97e3-712a0e5df2b8
-- title:
--   Corollary 1 — $\max_{i,j}|M^{\varepsilon,0}_{i,j} - (m_0)_{i,j}| \le C\varepsilon$
-- statement:
--   Assume the hypotheses of Theorem 1 ((G1), (G3), (G4), (G5), (24), $m_0, m_T \in \mathcal K$, $m_0 > 0$, and $\nu > 0$ or $\nu = 0$ with $m_T > 0$). There is a constant $C$, which may depend on $h$, $\Delta t$ and the other data but not on $\varepsilon$, such that for every $\varepsilon > 0$ and every solution $(U^\varepsilon, M^\varepsilon)$ of the penalized scheme (20)–(23),
--   $$
--   \max_{i,j}\big|M^{\varepsilon,0}_{i,j} - (m_0)_{i,j}\big| \le C\varepsilon. \tag{60}
--   $$
--
--   This improves the rate $\varepsilon^{1/2}$ of Proposition 2 to $\varepsilon$, and gives $M^0 = m_0$ for any limit of penalized solutions.
--
--   **Formalization Note** The constant is chosen once for the data, before $\varepsilon$ and the solution.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §3.2, Corollary 1, eq. (60), p. 16

import Mathlib
import Definitions.Def_MFGPlanning_Penalized_Grid
import Definitions.Def_MFGPlanning_Penalized_Hyp
import Definitions.Def_MFGPlanning_Penalized_Scheme

namespace MFGPlanning.Penalized

/-- Corollary 1, hal-00465404v1, §3.2, p. 16 (PDF 17), estimate (60): under the assumptions of
Theorem 1, the solution of the penalized system (20)–(23) satisfies
max_{i,j} |M^{ε,0}_{i,j} − (m_0)_{i,j}| ≤ C ε for a constant C which may depend on h and Δt but
not on ε.
Formalization Note: C is chosen after the data `d` and before ε and the solution. -/
theorem corollary_1 (d : Data) (hG1 : G1 d) (hG3 : G3 d) (hG4 : G4 d) (hG5 : G5 d) (hW : HypW d)
    (hm0 : InK d d.m0) (hmT : InK d d.mT) (hm0pos : ∀ p, 0 < d.m0 p)
    (hνmT : 0 < d.ν ∨ (d.ν = 0 ∧ ∀ p, 0 < d.mT p)) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ U M : Fin (d.NT + 1) → Pt d → ℝ, IsPenalizedSol d ε U M →
      ∀ p : Pt d, |M 0 p - d.m0 p| ≤ C * ε := by sorry

end MFGPlanning.Penalized
