-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_secScal_iff_resF
-- name    : GlobalTheory.ConstFam.secScal_iff_resF
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:16:23.455416+00:00
-- url     : https://prove2.me/theorems/4afa2a48-04fd-4d06-a11c-0afdfbff222b
-- title:
--   Const Fam: sec Scal iff res F
-- statement:
--   The Const Fam construction uses the sec Scal iff res F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsFETranslateFeTranslate.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsFETranslateFeTranslate.lean#L72-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.ConstFam.secScal_iff_resF {j : ℕ} {α : D.X} (s₁ : SecFMod D F j α) (s : SecBMod D j α) (r : R) :
    GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε j) s₁ (D.famφB α) (DegPre.famε j) s (DegPre.prB D F).left
      (scal (DegPre.BF D F).hom r) ↔ resF D F j α s = toF (R := R) F r • s₁ := by sorry
