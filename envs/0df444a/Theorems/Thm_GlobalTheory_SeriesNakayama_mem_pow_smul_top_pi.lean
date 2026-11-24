-- Prove2me | Theorems.Thm_GlobalTheory_SeriesNakayama_mem_pow_smul_top_pi
-- name    : GlobalTheory.SeriesNakayama.mem_pow_smul_top_pi
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:27.471117+00:00
-- url     : https://prove2.me/theorems/a672c1f3-29bd-46ae-9a34-567f826edb3d
-- title:
--   Series Nakayama: mem pow smul top pi
-- statement:
--   The Series Nakayama construction uses the mem pow smul top pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SpanModEquationsLift.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SpanModEquationsLift.lean#L15-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SpanModEquationsLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.SeriesNakayama

theorem GlobalTheory.SeriesNakayama.mem_pow_smul_top_pi {O ι : Type*} [CommRing O] (π : O) (n : ℕ) (x : ι → O) :
    x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O (ι → O)) ↔
      ∀ i, x i ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O O) := by sorry
