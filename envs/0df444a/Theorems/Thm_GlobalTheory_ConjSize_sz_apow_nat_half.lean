-- Prove2me | Theorems.Thm_GlobalTheory_ConjSize_sz_apow_nat_half
-- name    : GlobalTheory.ConjSize.sz_apow_nat_half
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:41:14.508513+00:00
-- url     : https://prove2.me/theorems/35d47464-ab04-4e80-8c1e-0cf97f278b15
-- title:
--   Conj Size: sz apow nat half
-- statement:
--   The Conj Size construction uses the sz apow nat half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L112-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/LocalEmbeddings/ArchSz.lean#L112-L119

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

theorem GlobalTheory.ConjSize.sz_apow_nat_half (u : kˣ) (h : apow u (1 / 2) ∈ Set.range ι) (n : ℕ) {c : ℝ} (hc : 1 ≤ c) (hu : nabs k u ≤ c) :
    Sz ι τ (apow u ((n : ℂ) / 2)) (c ^ n) := by sorry
