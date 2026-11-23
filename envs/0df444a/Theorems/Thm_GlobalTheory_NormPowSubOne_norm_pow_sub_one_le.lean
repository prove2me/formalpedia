-- Prove2me | Theorems.Thm_GlobalTheory_NormPowSubOne_norm_pow_sub_one_le
-- name    : GlobalTheory.NormPowSubOne.norm_pow_sub_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:48.895368+00:00
-- url     : https://prove2.me/theorems/634c4d35-28f0-4aa7-bb6b-eba1f420130c
-- title:
--   Norm Pow Sub One: norm pow sub one le
-- statement:
--   The Norm Pow Sub One construction uses the norm pow sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormPowSubOneLe.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormPowSubOneLe.lean#L7-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormPowSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.NormPowSubOne

theorem GlobalTheory.NormPowSubOne.norm_pow_sub_one_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] {ζ : K}
    (hζ : ‖ζ‖ = (1 : ℝ)) (a : ℕ) : ‖ζ ^ a - (1 : K)‖ ≤ ‖ζ - (1 : K)‖ := by sorry
