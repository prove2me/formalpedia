-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_basis_discr_associated_prod_jacobian
-- name    : GlobalTheory.T.exists_basis_discr_associated_prod_jacobian
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:34:24.849803+00:00
-- url     : https://prove2.me/theorems/b8c9e3ea-40cd-40b9-b610-1fd7f7a6a340
-- title:
--   T: exists basis discr associated prod jacobian
-- statement:
--   The T construction uses the exists basis discr associated prod jacobian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DiscrEqJacobianOfIntegralPointsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DiscrEqJacobianOfIntegralPointsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrEqJacobianOfIntegralPoints
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrEqJacobianOfIntegralPointsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_basis_discr_associated_prod_jacobian : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (g : ℕ) (Ix : Type) [Fintype Ix] [DecidableEq Ix] (F : Fin g → (MvPowerSeries (Fin g) O)) (e : Ix → ((MvPowerSeries (Fin g) O) →ₐ[O] O)), (∀ a i, e a (F i) = 0) → (∀ a i, e a (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) → (∀ G, (∀ a, e a G = 0) → G ∈ Ideal.span (Set.range F)) → (∃ c : O, c ≠ 0 ∧ ∀ t : Ix → O, ∃ G, ∀ a, e a G = c * t a) → ∃ β : Ix → (MvPowerSeries (Fin g) O), (∀ G, ∃! r : Ix → O, G - ∑ a, r a • β a ∈ Ideal.span (Set.range F)) ∧ (Matrix.of fun a a' => e a (β a')).det ≠ 0 ∧ Associated ((Matrix.of fun a a' => e a (β a')).det ^ 2) (∏ a, e a (Matrix.of fun i j => MvPowerSeries.pderiv O j (F i)).det) := by sorry
