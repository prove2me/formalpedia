-- Prove2me | Theorems.Thm_KelsoCrawford_NoCore_inequalities_24_to_27
-- name    : KelsoCrawford.NoCore.inequalities_24_to_27
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:14.595948+00:00
-- url     : https://prove2.me/theorems/58e34691-65a2-4cae-8b6f-face9f9d723b
-- title:
--   Section 6, p. 1503, (24)–(27) — the coalitions (j; {3}), (j; {1,2}), (k; {1}), (k; {3}) cannot strictly improve only if (24)–(27) hold
-- statement:
--   In the market of the example of Section 6, consider an allocation that assigns $\{1\}$ to firm $j$ and $\{2, 3\}$ to firm $k$, with salaries $s_{1j}$, $s_{2k}$, $s_{3k}$. If none of the four coalitions $(j; \{3\})$, $(j; \{1,2\})$, $(k; \{1\})$, $(k; \{3\})$ can strictly improve upon it with real salaries, then
--   $$\begin{aligned}
--   &(24)\quad 4 - s_{1j} + s_{3k} \ge 4\tfrac14, \\
--   &(25)\quad 4 - s_{1j} + s_{1j} + s_{2k} \ge 7\tfrac12, \\
--   &(26)\quad 7\tfrac12 - s_{2k} - s_{3k} + s_{1j} \ge 4\tfrac14, \\
--   &(27)\quad 7\tfrac12 - s_{2k} - s_{3k} + s_{3k} \ge 4.
--   \end{aligned}$$
--
--   Each inequality says that what the coalition can produce does not exceed what its members already receive.
--
--   **Formalization Note** The printed (24) reads $4 - s_{1j} + s_{3k} \le 4\tfrac14$. That is a misprint: coalition $(j; \{3\})$ cannot strictly improve exactly when $4\tfrac14 - s_{3k} \le 4 - s_{1j}$, i.e. $4 - s_{1j} + s_{3k} \ge 4\tfrac14$, and only this reading yields the paper's own consequence (24′) $s_{3k} - s_{1j} \ge \tfrac14$. The corrected inequality is stated. The paper asserts the implication from "cannot improve" to (24)–(27), which is what is stated. Workers $1, 2, 3$ are `0, 1, 2`, firms $j, k$ are `0, 1`, and the salary of worker $i$ at his or her own firm is `A.sal`.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1503, Section 6, eqs. (24)–(27) ((24) misprinted ≦, read ≧)

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Model
import Definitions.Def_KelsoCrawford_NoCore_Notions
import Definitions.Def_KelsoCrawford_NoCore_Example

namespace KelsoCrawford.NoCore

theorem inequalities_24_to_27 (A : Allocation (Fin 3) (Fin 2))
    (hj : A.hired 0 = {0}) (hk : A.hired 1 = {1, 2})
    (h24 : ¬ noCoreMarket.CoalitionCanStrictlyImprove KelsoCrawford.ContinuousCore.anySalary A 0 {2})
    (h25 : ¬ noCoreMarket.CoalitionCanStrictlyImprove KelsoCrawford.ContinuousCore.anySalary A 0 {0, 1})
    (h26 : ¬ noCoreMarket.CoalitionCanStrictlyImprove KelsoCrawford.ContinuousCore.anySalary A 1 {0})
    (h27 : ¬ noCoreMarket.CoalitionCanStrictlyImprove KelsoCrawford.ContinuousCore.anySalary A 1 {2}) :
    4 - A.sal 0 + A.sal 2 ≥ 17 / 4 ∧
    4 - A.sal 0 + A.sal 0 + A.sal 1 ≥ 15 / 2 ∧
    15 / 2 - A.sal 1 - A.sal 2 + A.sal 0 ≥ 17 / 4 ∧
    15 / 2 - A.sal 1 - A.sal 2 + A.sal 2 ≥ 4 := by sorry

end KelsoCrawford.NoCore
