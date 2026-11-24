-- Prove2me | Theorems.Thm_GlobalTheory_T_existsUnique_generator_extend_discreteValuationRing
-- name    : GlobalTheory.T.existsUnique_generator_extend_discreteValuationRing
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:36:22.893895+00:00
-- url     : https://prove2.me/theorems/34e35766-76b3-4cae-92e1-60628356e298
-- title:
--   T: exists Unique generator extend discrete Valuation Ring
-- statement:
--   The T construction uses the exists Unique generator extend discrete Valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueGeneratorExtendDiscreteValuationRingStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueGeneratorExtendDiscreteValuationRingStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRingStatement
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
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.T.existsUnique_generator_extend_discreteValuationRing : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t := by sorry
