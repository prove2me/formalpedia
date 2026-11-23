-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_secScal_iff
-- name    : GlobalTheory.FieldBaseChange.secScal_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:17:44.57043+00:00
-- url     : https://prove2.me/theorems/638cbf60-b7d5-4cb1-878d-48be222868ec
-- title:
--   Field Base Change: sec Scal iff
-- statement:
--   The Field Base Change construction uses the sec Scal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionPullOver.lean#L257-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionPullOver.lean#L257-L266

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}}
variable (π : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y)
variable {π} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
variable {π' : Y' ⟶ Spec (CommRingCat.of R')} {f : R →+* R'} {p : Y' ⟶ Y}
  (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) {φ' : K → (Y' ⟶ X)} (hφ : ∀ k, φ' k = p ≫ φ k)

theorem GlobalTheory.FieldBaseChange.secScal_iff (hL : L.IsLB) (s₁ : SecOver π' (LB.LinComb L φ' ε)) (s : SecOver π (LB.LinComb L φ ε))
    {S : Type} [CommRing S] (π₀ : Y' ⟶ Spec (CommRingCat.of S)) (g : S →+* R')
    (h₀ : π₀ = π' ≫ Spec.map (CommRingCat.ofHom g)) (c : S) :
    GeneratorPullback.SecScal L φ' ε s₁ φ ε s p (scal π₀ c) ↔ pullOver L ε hp hφ s = g c • s₁ := by sorry
