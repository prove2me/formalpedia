-- Prove2me | Theorems.Thm_GlobalTheory_FiniteQuotOmega_jacobian_smul_kaehler_eq_zero
-- name    : GlobalTheory.FiniteQuotOmega.jacobian_smul_kaehler_eq_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:43:39.374231+00:00
-- url     : https://prove2.me/theorems/b164756b-e75e-4171-acc1-b2bbdafa1775
-- title:
--   Finite Quot Omega: jacobian smul kaehler eq zero
-- statement:
--   The Finite Quot Omega construction uses the jacobian smul kaehler eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JacobianSmulKaehlerEqZero.lean#L105-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JacobianSmulKaehlerEqZero.lean#L105-L110

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

theorem GlobalTheory.FiniteQuotOmega.jacobian_smul_kaehler_eq_zero :
    ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] (σ : Type) [Fintype σ] [DecidableEq σ] (f : σ → MvPowerSeries σ T), Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) → ∀ ω : KaehlerDifferential T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)), (Ideal.Quotient.mk (Ideal.span (Set.range f)) (Matrix.det (Matrix.of fun i j => pderiv T j (f i)))) • ω = 0 := by sorry
