-- Prove2me | Theorems.Thm_KelsoCrawford_NoCore_firm_j_unique_demands
-- name    : KelsoCrawford.NoCore.firm_j_unique_demands
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:30.72338+00:00
-- url     : https://prove2.me/theorems/c2763e75-d8f6-4620-b992-879e8f02d67f
-- title:
--   Section 6, p. 1502 — firm j's unique preferred sets: {1, 2} at (3, 3, 3) with profit 1½, {3} at (3, 4, 3) with profit 1¼
-- statement:
--   Let $y^j$ be firm $j$'s technology from the example of Section 6, and consider the salary vectors $s^j = (3, 3, 3)$ and $\tilde s^j = (3, 4, 3)$ (salaries of workers $1, 2, 3$). Then $\{1, 2\}$ is the unique profit-maximizing set of workers at $s^j$, and $\{3\}$ is the unique one at $\tilde s^j$:
--   $$M^j(s^j) = \big\{\{1,2\}\big\}, \quad \pi^j(\{1,2\}; s^j) = 1\tfrac12, \qquad M^j(\tilde s^j) = \big\{\{3\}\big\}, \quad \pi^j(\{3\}; \tilde s^j) = 1\tfrac14.$$
--
--   This is the computation behind the failure of (GS) for firm $j$: raising only worker 2's salary makes the firm drop worker 1, whose salary did not change.
--
--   **Formalization Note** "Unique preferred set" is stated as: a set $C$ is demanded (maximizes profit over all $2^3$ sets) if and only if $C = \{1, 2\}$ (respectively $C = \{3\}$). Workers $1, 2, 3$ are `0, 1, 2`.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1502, Section 6

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Model
import Definitions.Def_KelsoCrawford_NoCore_Example

namespace KelsoCrawford.NoCore

theorem firm_j_unique_demands :
    (∀ C : Finset (Fin 3), KelsoCrawford.Process.IsDemanded techJ ![3, 3, 3] C ↔ C = {0, 1}) ∧
    KelsoCrawford.Process.profit techJ {0, 1} ![3, 3, 3] = 3 / 2 ∧
    (∀ C : Finset (Fin 3), KelsoCrawford.Process.IsDemanded techJ ![3, 4, 3] C ↔ C = {2}) ∧
    KelsoCrawford.Process.profit techJ {2} ![3, 4, 3] = 5 / 4 := by sorry

end KelsoCrawford.NoCore
