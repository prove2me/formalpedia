-- Prove2me | Theorems.Thm_GeneralCK_LimitTransfer_regularizedEntropyBound_implies_CK
-- name    : GeneralCK.LimitTransfer.regularizedEntropyBound_implies_CK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T22:22:14.36811+00:00
-- url     : https://prove2.me/theorems/dd3c7fef-7f15-4d17-a6d7-41b5a30c0665
-- title:
--   The regularized entropy bound implies the full Courtade–Kumar inequality
-- statement:
--   Assume RegularizedEntropyBound for every dimension, Boolean function, regularization parameter $0<\varepsilon<1/2$, and channel parameter $0<p<1/2$. Then GeneralCourtadeKumar holds. Continuity allows $\varepsilon\to0$, the finite-sum mutual-information identity converts the limit to the desired inequality, and channel symmetry supplies the remaining parameters.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/LimitTransfer.lean#L19-L49

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
import Definitions.Def_GeneralCK_limit_transfer
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
namespace GeneralCK.LimitTransfer
end GeneralCK.LimitTransfer
open GeneralCK GeneralCK.LimitTransfer
open scoped BigOperators

theorem GeneralCK.LimitTransfer.regularizedEntropyBound_implies_CK (hBound : RegularizedEntropyBound) :
    GeneralCourtadeKumar := by sorry
