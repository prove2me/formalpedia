-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_diagonal_menu_feasible
-- name    : IndependentInfoPricing.Main.diagonal_menu_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:13.727191+00:00
-- url     : https://prove2.me/theorems/c076e49d-eba1-4983-9a02-13c9debfc10f
-- title:
--   Lemma 3.3 — Feasibility of the diagonal menu
-- statement:
--   For the Section 3.1 parameters, the exact menu (29)–(30), with both free options, is feasible and admits an information-IC measurable implementation. Every diagonal type $v^{(i)}=(a^i,-b^i)$ has outside value zero and obtains utility zero from its intended option. It weakly prefers that option to every menu entry under the full four-rule experiment value:
--
--   $$V(v^{(i)},x)-p\le0\quad((x,p)\in M).$$
--
--   Under the highest-price tie convention the selected payment equals $p^{(i)}$. Thus its own option is a seller-favorable maximizer, including the separately defined last option. Feasibility covers the whole menu and all types; it does not discard the off-diagonal buyers.
--
--   Differences from the source:
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 3.3, printed pp.15–15 (PDF pp.17–17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Diagonal

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Lemma 3.3, pp.15–16 (PDF 17–18), including the full four-rule check after its proof. -/
theorem diagonal_menu_feasible (k n : ℕ) (h : FamilyParameters k n) :
    ValidMenu (diagonalMenu k n) ∧ ImplementsMenu (diagonalMenu k n) ∧
    ∀ i ∈ Finset.Icc 1 n,
      binaryValue (diagonalType k i) (diagonalAllocation k n i) - diagonalPrice k n i = 0 ∧
      outside (diagonalType k i) ≤ 0 ∧
      (∀ e ∈ diagonalMenu k n,
        binaryValue (diagonalType k i) e.1 - e.2 ≤ 0) ∧
      menuPayment true (diagonalMenu k n) (diagonalType k i) = diagonalPrice k n i := by sorry

end IndependentInfoPricing.Main
