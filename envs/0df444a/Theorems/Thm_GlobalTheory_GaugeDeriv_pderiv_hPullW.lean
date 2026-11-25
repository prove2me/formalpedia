-- Prove2me | Theorems.Thm_GlobalTheory_GaugeDeriv_pderiv_hPullW
-- name    : GlobalTheory.GaugeDeriv.pderiv_hPullW
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:33:39.646236+00:00
-- url     : https://prove2.me/theorems/ff5af381-254f-41a5-a9c5-db6f382df583
-- title:
--   Gauge Deriv: pderiv h Pull W
-- statement:
--   The Gauge Deriv construction uses the pderiv h Pull W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PderivLeafGaugeEqPairingAddIntegral.lean#L57-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PderivLeafGaugeEqPairingAddIntegral.lean#L57-L70

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SubstEqOfCoeffEqOfKilled
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivLeafGaugeEqPairingAddIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.GaugeDeriv
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable {ι ι' : Type} [Fintype ι] [Fintype ι']

theorem GlobalTheory.GaugeDeriv.pderiv_hPullW (H : MvPowerSeries (WV I) C) (e : ι → WV I → C) (g : Fin 2)
    (v' : ι' → I g → C) (b : ι') :
    MvPowerSeries.pderiv C (Sum.inr b) (hPullW H e (fun b => toW g (v' b))) =
      ∑ k, v' b k • hPullW (dVar ⟨g, k⟩ H) e (fun b => toW g (v' b)) := by sorry
