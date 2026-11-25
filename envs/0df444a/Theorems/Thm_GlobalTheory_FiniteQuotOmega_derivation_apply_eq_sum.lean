-- Prove2me | Theorems.Thm_GlobalTheory_FiniteQuotOmega_derivation_apply_eq_sum
-- name    : GlobalTheory.FiniteQuotOmega.derivation_apply_eq_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:09:26.67759+00:00
-- url     : https://prove2.me/theorems/8c94b5b9-a8ef-46ef-9aea-0138ef89d436
-- title:
--   Finite Quot Omega: derivation apply eq sum
-- statement:
--   The Finite Quot Omega construction uses the derivation apply eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JacobianSmulKaehlerEqZero.lean#L13-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JacobianSmulKaehlerEqZero.lean#L13-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JacobianSmulKaehlerEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FiniteQuotOmega
open MvPowerSeries IsLocalRing
open scoped TensorProduct
variable {T Q σ : Type*} [CommRing T] [CommRing Q] [Algebra T Q] [Fintype σ]

theorem GlobalTheory.FiniteQuotOmega.derivation_apply_eq_sum [IsNoetherianRing Q] {M : Type*} [AddCommGroup M] [Module T M]
    [Module Q M] [Module.Finite Q M] (φ : MvPowerSeries σ T →ₐ[T] Q)
    (hφ : Function.Surjective φ) (D : Derivation T Q M) (g : MvPowerSeries σ T) :
    D (φ g) = ∑ j, φ (pderiv T j g) • D (φ (X j)) := by sorry
