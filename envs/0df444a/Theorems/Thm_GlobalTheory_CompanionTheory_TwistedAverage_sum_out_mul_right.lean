-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_sum_out_mul_right
-- name    : GlobalTheory.CompanionTheory.TwistedAverage.sum_out_mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:05.842601+00:00
-- url     : https://prove2.me/theorems/587f5920-de28-411c-b96f-e641ebc38080
-- title:
--   Twisted Average: sum out mul right
-- statement:
--   The Twisted Average construction uses the sum out mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemTwKerIffAverage.lean#L35-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemTwKerIffAverage.lean#L35-L49

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

theorem GlobalTheory.CompanionTheory.TwistedAverage.sum_out_mul_right (N : Subgroup H) [N.Normal] [Fintype (H ⧸ N)] (f : H → V)
    (hf : ∀ x, ∀ k ∈ N, f (x * k) = f x) (l : H) :
    ∑ q : H ⧸ N, f (q.out * l) = ∑ q : H ⧸ N, f q.out := by sorry
