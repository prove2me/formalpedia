-- Prove2me | Theorems.Thm_GlobalTheory_polMod_mul_fg
-- name    : GlobalTheory.polMod_mul_fg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:14:06.425064+00:00
-- url     : https://prove2.me/theorems/7b27b6e4-db42-492a-b412-5226c6b9898f
-- title:
--   Global Theory: pol Mod mul fg
-- statement:
--   The Global Theory construction uses the pol Mod mul fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarizationLatticeFg.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarizationLatticeFg.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationLatticeFg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
open GlobalTheory

theorem GlobalTheory.polMod_mul_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) → IsUnit (polMod L) → (polMod L * L).toAddSubgroup.FG := by sorry
