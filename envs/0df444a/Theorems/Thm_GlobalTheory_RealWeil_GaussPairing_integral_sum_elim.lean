-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_GaussPairing_integral_sum_elim
-- name    : GlobalTheory.RealWeil.GaussPairing.integral_sum_elim
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:15:26.637657+00:00
-- url     : https://prove2.me/theorems/0bd5ec02-af1f-480b-94eb-d74292c543e1
-- title:
--   Gauss Pairing: integral sum elim
-- statement:
--   The Gauss Pairing construction uses the integral sum elim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianPairingUnitaryGroupTwoThree.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianPairingUnitaryGroupTwoThree.lean#L43-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingOfNormSqEqSumComplexCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.GaussPairing

theorem GlobalTheory.RealWeil.GaussPairing.integral_sum_elim {ι : Type} [Fintype ι] (F : (ι ⊕ ι → ℂ) → ℂ) (hF : Integrable F) :
    ∫ z : ι → ℂ, ∫ w : ι → ℂ, F (Sum.elim z w) = ∫ x, F x := by sorry
