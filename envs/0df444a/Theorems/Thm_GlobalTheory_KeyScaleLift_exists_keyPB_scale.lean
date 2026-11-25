-- Prove2me | Theorems.Thm_GlobalTheory_KeyScaleLift_exists_keyPB_scale
-- name    : GlobalTheory.KeyScaleLift.exists_keyPB_scale
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:23:25.805804+00:00
-- url     : https://prove2.me/theorems/65385311-dbea-4c07-b749-d48c3aa81e58
-- title:
--   Key Scale Lift: exists key PB scale
-- statement:
--   The Key Scale Lift construction uses the exists key PB scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsKeyPBScale.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsKeyPBScale.lean#L23-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LieBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ValueAtNormalForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsKeyPBScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyScaleLift

theorem GlobalTheory.KeyScaleLift.exists_keyPB_scale : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (y : KeyIn R) (x : KeyIn R') (a : Rˣ) (M : Matrix (Fin x.P.g) (Fin x.P.g) R), KeyPB x y f → IsUnit M.det → ∃ y₁ : KeyIn R, ∀ (t : x.P.L.Sec) (ht : _) (v : Fin x.P.g → (epsR R' ⟶ x.P.A)) (hv : _), (∀ i, t.f i = constFn x.P.A.hom _ (f a) * x.th.f i) → (∀ i, IsLieComb (fun k => f (M i k)) x.v (v i)) → KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, t, ht, v, hv⟩ y₁ f := by sorry
