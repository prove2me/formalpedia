-- Prove2me | Theorems.Thm_GlobalTheory_RankFibreKer_mem_coinv_of_finset_sum
-- name    : GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:13:48.874982+00:00
-- url     : https://prove2.me/theorems/dacc96ce-80ef-4ad9-8785-7a919deee189
-- title:
--   Rank Fibre Ker: mem coinv of finset sum
-- statement:
--   The Rank Fibre Ker construction uses the mem coinv of finset sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoinvariantOfLocallyConstantTwist.lean#L7-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoinvariantOfLocallyConstantTwist.lean#L7-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoinvariantOfLocallyConstantTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open GlobalTheory GlobalTheory.RankFibreKer

theorem GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ χ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (R : Finset (GL (Fin a) k)) (hΦ : Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)) (hχ : IsLocallyConstant χ)
    (h1 : ∀ Y, Φ Y = ∑ r ∈ R, χ ((r⁻¹).val * Y) * Φ Y)
    (h2 : ∀ Y, χ Y * ∑ r ∈ R, tw ν (a + b) r * Φ (r.val * Y) = 0) : Φ ∈ coinv ν β a (a + b) := by sorry
