-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_sum_out_refine
-- name    : GlobalTheory.CompanionTheory.TwistedAverage.sum_out_refine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:22.398939+00:00
-- url     : https://prove2.me/theorems/65167d19-c1b6-4c3f-b475-bcba162afe6e
-- title:
--   Twisted Average: sum out refine
-- statement:
--   The Twisted Average construction uses the sum out refine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemTwKerIffAverage.lean#L14-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemTwKerIffAverage.lean#L14-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemTwKerIffAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwistedAverage
open GlobalTheory.PRep
variable {H V : Type} [Group H] [AddCommGroup V]

theorem GlobalTheory.CompanionTheory.TwistedAverage.sum_out_refine {N K : Subgroup H} (hNK : N ≤ K) [Fintype (H ⧸ N)] [Fintype (H ⧸ K)]
    [Fintype (K ⧸ N.subgroupOf K)] (f : H → V) (hf : ∀ x, ∀ k ∈ K, f (x * k) = f x) :
    ∑ q : H ⧸ N, f q.out = Fintype.card (K ⧸ N.subgroupOf K) • ∑ q : H ⧸ K, f q.out := by sorry
