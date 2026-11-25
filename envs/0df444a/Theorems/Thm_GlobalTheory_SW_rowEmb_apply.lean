-- Prove2me | Theorems.Thm_GlobalTheory_SW_rowEmb_apply
-- name    : GlobalTheory.SW.rowEmb_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:30.129046+00:00
-- url     : https://prove2.me/theorems/c80ff574-b8dc-4738-a58d-860217d349ff
-- title:
--   SW: row Emb apply
-- statement:
--   The SW construction uses the row Emb apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L135-L136

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

theorem GlobalTheory.SW.rowEmb_apply {E m n : Type} [Field E] [Fintype n] (W : Matrix n m E) (t : n → E)
    (p : (E →+* ℂ) × m) : rowEmb W t p = p.1 ((t ᵥ* W) p.2) := by sorry

attribute [defeq] GlobalTheory.SW.rowEmb_apply
