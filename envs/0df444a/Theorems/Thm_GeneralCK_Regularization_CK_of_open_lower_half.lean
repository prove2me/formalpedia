-- Prove2me | Theorems.Thm_GeneralCK_Regularization_CK_of_open_lower_half
-- name    : GeneralCK.Regularization.CK_of_open_lower_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:22:36.244203+00:00
-- url     : https://prove2.me/theorems/e95f7442-ca23-456f-abc2-e6e16113b152
-- title:
--   Channel symmetry and endpoints reduce Courtade–Kumar to the open lower half
-- statement:
--   Assume the Courtade–Kumar inequality holds for every dimension and Boolean function whenever $0<p<1/2$. Then it holds for every $p\in[0,1]$, including $0,1/2,1$. The proof treats those endpoints and uses the equivalence between channel parameters $p$ and $1-p$ for the upper half. The conclusion is exactly the unrestricted GeneralCourtadeKumar proposition of the mission.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Regularization.lean#L76-L96

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
namespace GeneralCK.Regularization
end GeneralCK.Regularization
open GeneralCK GeneralCK.Regularization
open scoped BigOperators

theorem GeneralCK.Regularization.CK_of_open_lower_half
    (h : ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ),
      0 < p → p < 1 / 2 → mutualInformation f p ≤ 1 - H p) :
    GeneralCourtadeKumar := by sorry
