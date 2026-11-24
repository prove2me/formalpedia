-- Prove2me | Theorems.Thm_GlobalTheory_KS_ProdLift_app_appLE
-- name    : GlobalTheory.KS.ProdLift.app_appLE
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:44:59.225836+00:00
-- url     : https://prove2.me/theorems/91e2527b-06d3-4b01-b5db-9ca32a5ecda2
-- title:
--   Prod Lift: app app LE
-- statement:
--   The Prod Lift construction uses the app app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDerOfIsPushout.lean#L107-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDerOfIsPushout.lean#L107-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerOfIsPushout
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
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.ProdLift

theorem GlobalTheory.KS.ProdLift.app_appLE {Z Z₀ X Y : Scheme.{0}} {p : Z ⟶ X} {p₀ : Z₀ ⟶ Y} {m : Y ⟶ X} {m₂ : Z₀ ⟶ Z}
    (hp : m₂ ≫ p = p₀ ≫ m) {W : X.Opens} {Q : Z.Opens} (h : Q ≤ p ⁻¹ᵁ W)
    (h' : m₂ ⁻¹ᵁ Q ≤ p₀ ⁻¹ᵁ m ⁻¹ᵁ W) (f : Γ(X, W)) :
    (m₂.app Q).hom ((p.appLE W Q h).hom f) = (p₀.appLE _ _ h').hom ((m.app W).hom f) := by sorry
