-- Prove2me | Theorems.Thm_GlobalTheory_groupChunk_extend
-- name    : GlobalTheory.groupChunk_extend
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:54:10.347863+00:00
-- url     : https://prove2.me/theorems/440d0009-3fa9-4b32-8da0-43438ef43008
-- title:
--   Global Theory: group Chunk extend
-- statement:
--   The Global Theory construction uses the group Chunk extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHomOfBigCellGenericRelations.lean#L11-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHomOfBigCellGenericRelations.lean#L11-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomOfBigCellGenericRelations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory

theorem GlobalTheory.groupChunk_extend {G H : Type} [Group G] [Group H] (C : G → Prop) (f : G → H)
    (hmul : ∀ x y, C x → C y → C (x * y) → f (x * y) = f x * f y)
    (hgen : ∀ s : Finset G, ∃ u : G, ∀ g ∈ s, C (g * u)) :
    ∃ Φ : G →* H, ∀ g u, C u → C (g * u) → Φ g = f (g * u) * (f u)⁻¹ := by sorry
