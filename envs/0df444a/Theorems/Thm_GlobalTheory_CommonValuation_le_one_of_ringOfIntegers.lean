-- Prove2me | Theorems.Thm_GlobalTheory_CommonValuation_le_one_of_ringOfIntegers
-- name    : GlobalTheory.CommonValuation.le_one_of_ringOfIntegers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:57.288087+00:00
-- url     : https://prove2.me/theorems/5608ccc4-2be9-4562-95ad-1fb8d596a481
-- title:
--   Common Valuation: le one of ring Of Integers
-- statement:
--   The Common Valuation construction uses the le one of ring Of Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RamificationIndexValuationCompat.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RamificationIndexValuationCompat.lean#L73-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteSeparableCompositum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationIndexValuationCompat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CommonValuation

theorem GlobalTheory.CommonValuation.le_one_of_ringOfIntegers {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (u : Valuation F Γ)
    (r : 𝓞 F) : u (algebraMap (𝓞 F) F r) ≤ 1 := by sorry
