-- Prove2me | Theorems.Thm_GlobalTheory_DiscrJacobianBlocks_exists_factor_associated_jacobian
-- name    : GlobalTheory.DiscrJacobianBlocks.exists_factor_associated_jacobian
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:51:15.428991+00:00
-- url     : https://prove2.me/theorems/869cd78a-d376-4faa-ba47-81367bb3acac
-- title:
--   Discr Jacobian Blocks: exists factor associated jacobian
-- statement:
--   The Discr Jacobian Blocks construction uses the exists factor associated jacobian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsFactorAssociatedJacobian.lean#L33-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsFactorAssociatedJacobian.lean#L33-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrEqJacobianOfIntegralPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsFactorAssociatedJacobian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.DiscrJacobianBlocks

theorem GlobalTheory.DiscrJacobianBlocks.exists_factor_associated_jacobian : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (g d N : ℕ) (Y : Type) (p : Fin d → Y) (F : Y → Fin g → (MvPowerSeries (Fin g) O)) (ρ : Y → Fin N → (MvPowerSeries (Fin g) O)) (e : Fin d → ((MvPowerSeries (Fin g) O) →ₐ[O] O)) (u : Fin d → Oˣ) (ev : Matrix (Fin d) (Fin N) O), (∀ a i, e a (F (p a) i) = 0) → (∀ a i, e a (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) → (∀ a k, ev a k = u a * e a (ρ (p a) k)) → (∀ G : Y → (MvPowerSeries (Fin g) O), ∃ v : Fin N → O, ∀ y, G y - ∑ k, v k • ρ y k ∈ Ideal.span (Set.range (F y))) → (∀ v, ev.mulVec v = 0 → ∀ y, ∑ k, v k • ρ y k ∈ Ideal.span (Set.range (F y))) → (∃ c : O, c ≠ 0 ∧ ∀ t, ∃ v, ev.mulVec v = c • t) → ∃ (ev₀ : Matrix (Fin d) (Fin N) O) (Pm : Matrix (Fin d) (Fin d) O), ev = Pm * ev₀ ∧ Pm.det ≠ 0 ∧ Function.Surjective ev₀.mulVec ∧ Associated (Pm.det ^ 2) (∏ a, e a (Matrix.of fun i j => MvPowerSeries.pderiv O j (F (p a) i)).det) := by sorry
