-- Prove2me | Theorems.Thm_GlobalTheory_EndCalc_end_calculus
-- name    : GlobalTheory.EndCalc.end_calculus
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:04:40.151307+00:00
-- url     : https://prove2.me/theorems/18a89458-eb94-4512-bebd-7860abfa268e
-- title:
--   End Calc: end calculus
-- statement:
--   The End Calc construction uses the end calculus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/UniformizationEndomorphismCalculus.lean#L355-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/UniformizationEndomorphismCalculus.lean#L355-L366

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniformizationEndomorphismOfLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UniformizationEndomorphismCalculus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.EndCalc
variable {R : Type} [CommRing R] [IsDomain R]

theorem GlobalTheory.EndCalc.end_calculus : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ E E' E'' : EndU U.toUnifPre, (∀ g : GtPtF D.toPre F, ∃! g', E.Act g g') ∧ (∀ g₁ g₂ g₃ g₁' g₂' g₃' : GtPtF D.toPre F, g₁.IsAdd g₂ g₃ → E.Act g₁ g₁' → E.Act g₂ g₂' → E.Act g₃ g₃' → g₁'.IsAdd g₂' g₃') ∧ (∀ t (g g' : GtPtF D.toPre F), IsTor t g → E.Act g g' → IsTor (t.comp (AddMonoidHom.toMultiplicative E.h)) g') ∧ (E.aG = E'.aG → E.aB = E'.aB ∧ E.h = E'.h ∧ ∀ g g' : GtPtF D.toPre F, E.Act g g' ↔ E'.Act g g') ∧ (E''.aG = E.aG * E'.aG → E''.aB = E.aB * E'.aB ∧ E''.h = E.h + E'.h ∧ ∀ g g₁ g₂ g₃ : GtPtF D.toPre F, E.Act g g₁ → E'.Act g g₂ → g₁.IsAdd g₂ g₃ → E''.Act g g₃) ∧ (E''.aG = E.aG ≫ E'.aG → E''.aB = E.aB ≫ E'.aB ∧ E''.h = E.h.comp E'.h ∧ ∀ g g₁ g₂ : GtPtF D.toPre F, E.Act g g₁ → E'.Act g₁ g₂ → E''.Act g g₂) := by sorry
