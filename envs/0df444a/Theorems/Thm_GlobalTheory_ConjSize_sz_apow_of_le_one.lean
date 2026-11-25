-- Prove2me | Theorems.Thm_GlobalTheory_ConjSize_sz_apow_of_le_one
-- name    : GlobalTheory.ConjSize.sz_apow_of_le_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:38.71767+00:00
-- url     : https://prove2.me/theorems/3998820a-4dfe-5104-bd7a-0a0547f64271
-- title:
--   Conj Size: sz apow of le one
-- statement:
--   The Conj Size construction uses the sz apow of le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L121-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L121-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AutomorphicArithmetic_LocalEmbeddings_ArchSz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open GlobalTheory GlobalTheory.ConjSize
variable {K : Type} [Field K] (ι τ : K →+* ℂ)
variable {ι τ}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.ConjSize.sz_apow_of_le_one (u : kˣ) (h : apow u (1 / 2) ∈ Set.range ι) (n : ℕ) (hu : valuation k (u : k) ≤ 1) :
    Sz ι τ (apow u ((n : ℂ) / 2)) 1 := by sorry
