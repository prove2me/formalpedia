-- Prove2me | Theorems.Thm_GlobalTheory_SectionsDescent_exists_coord_sec
-- name    : GlobalTheory.SectionsDescent.exists_coord_sec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:51:52.545203+00:00
-- url     : https://prove2.me/theorems/cc4d564c-c583-4421-a505-976dfe7382b9
-- title:
--   Sections Descent: exists coord sec
-- statement:
--   The Sections Descent construction uses the exists coord sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsExtensionAffine.lean#L153-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsExtensionAffine.lean#L153-L167

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
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
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.SectionsDescent
open GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F] {Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of K)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap K F))))

theorem GlobalTheory.SectionsDescent.exists_coord_sec {ℓ : F →ₗ[K] K}
    (Λ : ∀ V : Y.Opens, IsAffineOpen V → FnOver π' (p ⁻¹ᵁ V) →+ FnOver π V)
    (hΛ : ∀ V hV, IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ V))) ℓ (Λ V hV)) {M : LB Y} (t : (M.pull p).Sec) :
    ∃ s : M.Sec, ∀ j V hV (h : V ≤ M.U j), rs h (s.f j) = Λ V hV (rs (pre_mono p h) (loc t j)) := by sorry
