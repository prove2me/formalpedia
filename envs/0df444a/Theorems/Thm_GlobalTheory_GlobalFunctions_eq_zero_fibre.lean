-- Prove2me | Theorems.Thm_GlobalTheory_GlobalFunctions_eq_zero_fibre
-- name    : GlobalTheory.GlobalFunctions.eq_zero_fibre
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:55:52.613983+00:00
-- url     : https://prove2.me/theorems/b147e281-ad05-4fe1-bf15-abb709985ab1
-- title:
--   Global Functions: eq zero fibre
-- statement:
--   The Global Functions construction uses the eq zero fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean#L194-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoAppTopOfIsAffine.lean#L194-L232

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GlobalFunctions
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  {X : Scheme.{0}}

theorem GlobalTheory.GlobalFunctions.eq_zero_fibre (p : X ⟶ Spec (.of R)) [UniversallyClosed p] [GeometricallyIntegral p]
    (i : Spec (.of B) ⟶ X) [Flat i] [Surjective i] [QuasiCompact i] (f g : B →ₐ[R] C)
    (H : IsPullback (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) i i)
    (hφ : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R B))) (r : B →ₐ[R] R)
    (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] B)
    (hx : f.toLinearMap.baseChange k x = g.toLinearMap.baseChange k x)
    (hr : r.toLinearMap.baseChange k x = 0) : x = 0 := by sorry
