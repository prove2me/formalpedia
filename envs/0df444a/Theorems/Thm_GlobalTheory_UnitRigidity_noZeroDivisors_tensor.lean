-- Prove2me | Theorems.Thm_GlobalTheory_UnitRigidity_noZeroDivisors_tensor
-- name    : GlobalTheory.UnitRigidity.noZeroDivisors_tensor
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:20:16.702439+00:00
-- url     : https://prove2.me/theorems/102557c0-8cb8-4864-b48c-22d46e7ca3f7
-- title:
--   Unit Rigidity: no Zero Divisors tensor
-- statement:
--   The Unit Rigidity construction uses the no Zero Divisors tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedOfIsPullbackOfSurjective.lean#L284-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedOfIsPullbackOfSurjective.lean#L284-L296

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnitRigidity
open scoped TensorProduct

theorem GlobalTheory.UnitRigidity.noZeroDivisors_tensor {K A : Type} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (g : Spec (.of A) ⟶ X) [IsOpenImmersion g]
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (F : Type) [Field F] [Algebra K F] : NoZeroDivisors (F ⊗[K] A) := by sorry
