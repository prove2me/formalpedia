-- Prove2me | Theorems.Thm_IncompleteProc_English_proposition_1
-- name    : IncompleteProc.English.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:41.014799+00:00
-- url     : https://prove2.me/theorems/e1a6c251-4a3a-487c-ba3b-4ff0b1859574
-- title:
--   Proposition 1, p. 7 (PDF 8) — allocation (3)–(4) with the transfers of p. 15 is IC, IR and maximizes the buyer surplus over complete contracts
-- statement:
--   Consider the direct mechanism of Proposition 1, with transfers $t^i(C) = T(c^i)$ from the proof:
--   - supplier $i$ supplies in period 1 iff $c^i = \min\{c^1, \dots, c^n\}$ and $c^i \le c^\star_1$ (3);
--   - he supplies in period 2 in state $\omega$ iff, in addition, $k(c^i, \omega) \le k(c^\star_2(\omega), \omega)$ (4).
--
--   This mechanism is admissible, incentive compatible and individually rational. Its buyer surplus is the greatest buyer surplus among all admissible, incentive-compatible and individually rational direct mechanisms:
--   $$\mathrm{BS}(x^\star, t^\star) = \max\{\mathrm{BS}(x, t) : (x, t) \text{ admissible, IC, IR}\}.$$
--
--   This is the complete-contract benchmark: the largest surplus the buyer can secure when she commits to a two-period contract in period 1. Proposition 3 shows that an English auction followed by a spot offer attains the same value without such commitment.
--
--   **Formalization Note** "The allocation that maximizes the buyer surplus" is stated as optimality of the mechanism over the whole class, with the attaining mechanism exhibited (a maximum, not a supremum). Ties go to the lowest index, which the page allows (footnote 9). Under the unconditional reading of $x_2$, (4) carries the extra conjunct $c^i \le c^\star_1$: without it the mechanism would buy in period 2 from a supplier it did not buy from in period 1. The thresholds are crossing points and $A(c) = \Omega(c)$, as explained in the model definition.
-- source:
--   Gretschko & Pollrich, Incomplete Contracts in Dynamic Procurement, ZEW Discussion Paper No. 19-040 (Sept. 2019; SSRN 3466701), p. 7 (PDF 8), Proposition 1, eqs. (3)–(4); pp. 14–16 (PDF 15–17), proof of Proposition 1 (transfer rule T, p. 15)

import Mathlib
import Definitions.Def_IncompleteProc_English_Model

namespace IncompleteProc.English

open MeasureTheory

/-- Proposition 1 (p. 7) with the transfer rule of its proof (p. 15): the direct mechanism with
allocation (3)–(4) and transfers `tⁱ(C) = T(cⁱ)` is admissible, incentive compatible and
individually rational, and its buyer surplus is the greatest buyer surplus among all admissible,
incentive-compatible, individually rational direct mechanisms. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) :
    E.optMech.Admissible E ∧ E.optMech.IsIC E ∧ E.optMech.IsIR E ∧
      IsGreatest E.feasibleSurplus (E.optMech.buyerSurplus E) := by sorry

end IncompleteProc.English
