-- Prove2me | Theorems.Thm_MFGPlanning_Penalized_proposition_3
-- name    : MFGPlanning.Penalized.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:59:24.739895+00:00
-- url     : https://prove2.me/theorems/bd20c9d2-33fc-4c35-ae14-8146d1d8424c
-- title:
--   Proposition 3 — $\max_{n,i,j}|U^{\varepsilon,n}_{i,j}| \le C$ uniformly in $\varepsilon$
-- statement:
--   Assume the hypotheses of Theorem 1 ((G1), (G3), (G4), (G5), (24), $m_0, m_T \in \mathcal K$, $m_0 > 0$, and $\nu > 0$ or $\nu = 0$ with $m_T > 0$). There is a constant $C$, which may depend on $h$, $\Delta t$ and the other data but not on $\varepsilon$, such that for every $\varepsilon > 0$ and every solution $(U^\varepsilon, M^\varepsilon)$ of the penalized scheme (20)–(23),
--   $$
--   \max_{n,i,j}\big|U^{\varepsilon,n}_{i,j}\big| \le C. \tag{54}
--   $$
--
--   The uniform bound gives compactness of the value functions $U^\varepsilon$ as $\varepsilon \to 0$, which is what passing to the limit in Proposition 4 needs.
--
--   **Formalization Note** The constant is chosen once for the data, before $\varepsilon$ and the solution, and the bound is asserted for every $\varepsilon > 0$, as printed.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §3.2, Proposition 3, eq. (54), p. 15

import Mathlib
import Definitions.Def_MFGPlanning_Penalized_Grid
import Definitions.Def_MFGPlanning_Penalized_Hyp
import Definitions.Def_MFGPlanning_Penalized_Scheme

namespace MFGPlanning.Penalized

/-- Proposition 3, hal-00465404v1, §3.2, p. 15 (PDF 16), estimate (54): under the assumptions of
Theorem 1, the solution of the penalized system (20)–(23) satisfies max_{n,i,j} |U^{ε,n}_{i,j}| ≤ C
for a constant C which may depend on h and Δt but not on ε.
Formalization Note: C is chosen after the data `d` and before ε and the solution; the bound is
asserted for every ε > 0 (as printed) and every solution. -/
theorem proposition_3 (d : Data) (hG1 : G1 d) (hG3 : G3 d) (hG4 : G4 d) (hG5 : G5 d) (hW : HypW d)
    (hm0 : InK d d.m0) (hmT : InK d d.mT) (hm0pos : ∀ p, 0 < d.m0 p)
    (hνmT : 0 < d.ν ∨ (d.ν = 0 ∧ ∀ p, 0 < d.mT p)) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ U M : Fin (d.NT + 1) → Pt d → ℝ, IsPenalizedSol d ε U M →
      ∀ (n : Fin (d.NT + 1)) (p : Pt d), |U n p| ≤ C := by sorry

end MFGPlanning.Penalized
