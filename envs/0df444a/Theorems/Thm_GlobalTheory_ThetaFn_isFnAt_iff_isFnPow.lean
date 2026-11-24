-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFn_isFnAt_iff_isFnPow
-- name    : GlobalTheory.ThetaFn.isFnAt_iff_isFnPow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:21:28.402797+00:00
-- url     : https://prove2.me/theorems/1970c606-0030-4e50-9dd1-970802257ba4
-- title:
--   Theta Fn: is Fn At iff is Fn Pow
-- statement:
--   The Theta Fn construction uses the is Fn At iff is Fn Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L442-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L442-L461

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}
variable (u p)

theorem GlobalTheory.ThetaFn.isFnAt_iff_isFnPow (n : ℕ) (s : LB.Sec (LPow A L n T)) (θ : (Fin g → ℂ) → ℂ) :
    IsFnAt u p n s θ ↔ u.IsFnPow n (toFibre L p n s) θ := by sorry
