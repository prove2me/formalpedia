-- Prove2me | Theorems.Thm_GlobalTheory_SW_SwdHeat_isHeat_sub
-- name    : GlobalTheory.SW.SwdHeat.isHeat_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:15:04.059956+00:00
-- url     : https://prove2.me/theorems/72b1e17e-3b52-46b0-9725-bfca6a9c2afd
-- title:
--   Swd Heat: is Heat sub
-- statement:
--   The Swd Heat construction uses the is Heat sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatSwd.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatSwd.lean#L30-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThHStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisensteinSeriesOfSchwartzIsHolomorphicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatSwd
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SwdHeat
open GlobalTheory.SW.EisHeat
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

theorem GlobalTheory.SW.SwdHeat.isHeat_sub {D D' : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ} (hD : IsHeat Ψ D)
    (hD' : IsHeat Ψ D') : IsHeat Ψ fun Z z z' => D Z z z' - D' Z z z' := by sorry
