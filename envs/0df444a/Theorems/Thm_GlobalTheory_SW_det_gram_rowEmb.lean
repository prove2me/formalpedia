-- Prove2me | Theorems.Thm_GlobalTheory_SW_det_gram_rowEmb
-- name    : GlobalTheory.SW.det_gram_rowEmb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:26.023799+00:00
-- url     : https://prove2.me/theorems/9b7c3754-5da1-458b-9837-53e7d1a932e6
-- title:
--   SW: det gram row Emb
-- statement:
--   The SW construction uses the det gram row Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L140-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L140-L170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
open Classical

theorem GlobalTheory.SW.det_gram_rowEmb {E m : Type} [Field E] [NumberField E] [Fintype m] {N : ℕ}
    (W : Matrix (Fin N) m E) (ω : (E →+* ℂ) → E) :
    (((gram ℝ fun p : Fin N × (E →+* ℂ) => rowEmb W (Pi.single p.1 (ω p.2))).det : ℝ) : ℂ) =
      (normSq (Matrix.of fun k σ : E →+* ℂ => σ (ω k)).det : ℂ) ^ N *
        ∏ σ : E →+* ℂ, (W.map σ * (W.map σ)ᴴ).det := by sorry
