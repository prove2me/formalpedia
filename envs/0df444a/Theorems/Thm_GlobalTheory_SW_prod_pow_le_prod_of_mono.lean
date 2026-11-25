-- Prove2me | Theorems.Thm_GlobalTheory_SW_prod_pow_le_prod_of_mono
-- name    : GlobalTheory.SW.prod_pow_le_prod_of_mono
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:07:55.099286+00:00
-- url     : https://prove2.me/theorems/5aa8198e-5b22-4df3-8d00-67dc101dbc3d
-- title:
--   SW: prod pow le prod of mono
-- statement:
--   The SW construction uses the prod pow le prod of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L38-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L38-L50

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

theorem GlobalTheory.SW.prod_pow_le_prod_of_mono (l : ℕ → ℝ) (hl : ∀ i, 0 ≤ l i) (d N : ℕ)
    (hm : ∀ i j, i ≤ j → j ≤ d * N → l i ≤ l j) :
    ∏ i ∈ Finset.range N, l (d * i + 1) ^ d ≤ ∏ j ∈ Finset.range (d * N), l (j + 1) := by sorry
