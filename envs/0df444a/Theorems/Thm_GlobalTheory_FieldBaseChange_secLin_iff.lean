-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_secLin_iff
-- name    : GlobalTheory.FieldBaseChange.secLin_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:28.860487+00:00
-- url     : https://prove2.me/theorems/5c031f4a-afa2-4a8d-ab8c-8ab36707deb1
-- title:
--   Field Base Change: sec Lin iff
-- statement:
--   The Field Base Change construction uses the sec Lin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionPullOver.lean#L268-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionPullOver.lean#L268-L279

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

theorem GlobalTheory.FieldBaseChange.secLin_iff (hL : L.IsLB) {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ} (s₁ : SecOver π' (LB.LinComb L φ₁ ε₁))
    {n : ℕ} (s : Fin n → LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (c : Fin n → R')
    (t : Fin n → SecOver π' (LB.LinComb L φ₁ ε₁))
    (ht : ∀ i y J, Good L y J → sval (t i) (𝟙 Y') y J = sval (s i) (𝟙 Y' ≫ h) y J) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h (fun i => scal π' (c i)) ↔ s₁ = ∑ i, c i • t i := by sorry
