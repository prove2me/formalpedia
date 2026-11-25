-- Prove2me | Theorems.Thm_GlobalTheory_GaugeDeriv_constantCoeff_upG
-- name    : GlobalTheory.GaugeDeriv.constantCoeff_upG
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:33:33.94003+00:00
-- url     : https://prove2.me/theorems/2dcb3fd0-2772-4860-a6bb-12c8832548e8
-- title:
--   Gauge Deriv: constant Coeff up G
-- statement:
--   The Gauge Deriv construction uses the constant Coeff up G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PderivLeafGaugeEqPairingAddIntegral.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PderivLeafGaugeEqPairingAddIntegral.lean#L72-L77

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

theorem GlobalTheory.GaugeDeriv.constantCoeff_upG (g : Fin 2) {F : MvPowerSeries (I g) C}
    (hF : MvPowerSeries.constantCoeff F = 0) : MvPowerSeries.constantCoeff (upG g F) = 0 := by sorry
