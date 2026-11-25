-- Prove2me | Theorems.Thm_GlobalTheory_FiniteQuotOmega_det_smul_kaehler_eq_zero
-- name    : GlobalTheory.FiniteQuotOmega.det_smul_kaehler_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:09:59.213806+00:00
-- url     : https://prove2.me/theorems/537a445a-5543-4f56-880d-f2429ce06822
-- title:
--   Finite Quot Omega: det smul kaehler eq zero
-- statement:
--   The Finite Quot Omega construction uses the det smul kaehler eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JacobianSmulKaehlerEqZero.lean#L70-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JacobianSmulKaehlerEqZero.lean#L70-L101

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

theorem GlobalTheory.FiniteQuotOmega.det_smul_kaehler_eq_zero [DecidableEq σ] [IsNoetherianRing T] [Module.Finite T Q]
    (φ : MvPowerSeries σ T →ₐ[T] Q) (hφ : Function.Surjective φ) (f : σ → MvPowerSeries σ T)
    (hf : ∀ i, φ (f i) = 0) (ω : KaehlerDifferential T Q) :
    φ (Matrix.det (Matrix.of fun i j => pderiv T j (f i))) • ω = 0 := by sorry
