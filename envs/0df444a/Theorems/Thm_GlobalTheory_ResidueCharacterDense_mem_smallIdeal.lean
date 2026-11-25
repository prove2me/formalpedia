-- Prove2me | Theorems.Thm_GlobalTheory_ResidueCharacterDense_mem_smallIdeal
-- name    : GlobalTheory.ResidueCharacterDense.mem_smallIdeal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:26:59.806046+00:00
-- url     : https://prove2.me/theorems/34010e28-cf25-4814-be86-2c49a5424eb5
-- title:
--   Residue Character Dense: mem small Ideal
-- statement:
--   The Residue Character Dense construction uses the mem small Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L144-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L144-L145

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense

theorem GlobalTheory.ResidueCharacterDense.mem_smallIdeal {F Ω : Type} [Field F] [NormedField Ω] [IsUltrametricDist Ω]
    (σ : F →+* Ω) (x : 𝓞 F) : x ∈ smallIdeal σ ↔ ‖σ x‖ < 1 := by sorry
