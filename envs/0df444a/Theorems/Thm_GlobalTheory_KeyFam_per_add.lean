-- Prove2me | Theorems.Thm_GlobalTheory_KeyFam_per_add
-- name    : GlobalTheory.KeyFam.per_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:17.770819+00:00
-- url     : https://prove2.me/theorems/0c31cea5-36b5-4d5c-915d-5e6cc7a22eca
-- title:
--   Key Fam: per add
-- statement:
--   The Key Fam construction uses the per add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/KeyFormula/GeomIntSelf.lean#L76-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/KeyFormula/GeomIntSelf.lean#L76-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyFam
open GlobalTheory.KeyPow
variable {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S S' : Scheme.{0}} {s : S ⟶ Sp o}

theorem GlobalTheory.KeyFam.per_add {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g ⊕ Fin g → ℤ) :
    per τ (a + b) = per τ a + per τ b := by sorry
