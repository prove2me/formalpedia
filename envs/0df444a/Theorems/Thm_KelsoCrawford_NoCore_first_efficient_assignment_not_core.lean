-- Prove2me | Theorems.Thm_KelsoCrawford_NoCore_first_efficient_assignment_not_core
-- name    : KelsoCrawford.NoCore.first_efficient_assignment_not_core
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:27.328658+00:00
-- url     : https://prove2.me/theorems/2c554597-bb3e-4489-a79e-069cf90c2942
-- title:
--   Section 6, p. 1503 — (25) and (27) force s₂ₖ = 3½, and then (24′), (26′) contradict: j ← {1}, k ← {2, 3} is not part of a core allocation
-- statement:
--   In the market of the example of Section 6, no allocation that assigns $\{1\}$ to firm $j$ and $\{2, 3\}$ to firm $k$ is a core allocation (D3) with continuously variable salaries, whatever the salaries $s_{1j}$, $s_{2k}$, $s_{3k}$.
--
--   In the paper, (25) and (27) give $s_{2k} = 3\tfrac12$, after which (24) and (26) become $s_{3k} - s_{1j} \ge \tfrac14$ and $s_{3k} - s_{1j} \le -\tfrac14$, which are incompatible. By the symmetry of the example (workers $1 \leftrightarrow 3$, firms $j \leftrightarrow k$), the other efficient assignment is excluded in the same way.
--
--   **Formalization Note** Workers $1, 2, 3$ are `0, 1, 2` and firms $j, k$ are `0, 1`; the assignment is fixed through the sets of workers each firm hires.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1503–1504, Section 6, eqs. (24′), (26′)

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Model
import Definitions.Def_KelsoCrawford_NoCore_Example

namespace KelsoCrawford.NoCore

theorem first_efficient_assignment_not_core (A : Allocation (Fin 3) (Fin 2))
    (hj : A.hired 0 = {0}) (hk : A.hired 1 = {1, 2}) :
    ¬ noCoreMarket.IsCore KelsoCrawford.ContinuousCore.anySalary A := by sorry

end KelsoCrawford.NoCore
