-- Prove2me | Theorems.Thm_GlobalTheory_SW_det_denom_ne_zero
-- name    : GlobalTheory.SW.det_denom_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:12.78679+00:00
-- url     : https://prove2.me/theorems/a326bcea-d91a-4355-98fa-e530d4367416
-- title:
--   SW: det denom ne zero
-- statement:
--   The SW construction uses the det denom ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NormDetDenomLeRankOne.lean#L55-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NormDetDenomLeRankOne.lean#L55-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
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
variable {N : ℕ}

theorem GlobalTheory.SW.det_denom_ne_zero (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hp : (C * Cᴴ + D * Dᴴ).PosDef) (hZ : (imH Z).PosDef) : (C * Z + D).det ≠ 0 := by sorry
