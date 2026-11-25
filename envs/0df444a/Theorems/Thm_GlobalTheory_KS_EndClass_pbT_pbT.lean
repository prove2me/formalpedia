-- Prove2me | Theorems.Thm_GlobalTheory_KS_EndClass_pbT_pbT
-- name    : GlobalTheory.KS.EndClass.pbT_pbT
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:08:47.883126+00:00
-- url     : https://prove2.me/theorems/bc97bc41-5be3-4f08-95e2-28a8de365b95
-- title:
--   End Class: pb T pb T
-- statement:
--   The End Class construction uses the pb T pb T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassCohomologousAlongEndomorphism.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerClassCohomologousAlongEndomorphism.lean#L20-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivationsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerClassCohomologousAlongEndomorphism
import Theorems.Thm_GlobalTheory_KS_InvField_pbT_pbT
import Theorems.Thm_GlobalTheory_KS_InvHom_pbT_pbT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EndClass
variable {X Y Z T : Scheme.{0}}

theorem GlobalTheory.KS.EndClass.pbT_pbT (t : T ⟶ Z) (f : Z ⟶ Y) {O₀ : Y.Opens} {O₁ : Z.Opens} {O₂ : T.Opens} (h₁ : O₁ ≤ f ⁻¹ᵁ O₀)
    (h₂ : O₂ ≤ t ⁻¹ᵁ O₁) (s : Γ(Y, O₀)) : pbT t (pbT f s O₁) O₂ = pbT (t ≫ f) s O₂ := by sorry
