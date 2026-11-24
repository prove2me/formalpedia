-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_con_of_not_precedes
-- name    : GlobalTheory.CompanionTheory.MultiSeg.Rank.con_of_not_precedes
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:53:13.432927+00:00
-- url     : https://prove2.me/theorems/024291fe-f88c-4a92-9ffc-e220a5c22324
-- title:
--   Rank: con of not precedes
-- statement:
--   The Rank construction uses the con of not precedes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L206-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ShuffleWeightSquareLengthLt.lean#L206-L252

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Zc.Comb
open Classical
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MultiSeg GlobalTheory.CompanionTheory.MultiSeg.Rank
variable {T : Type u}

theorem GlobalTheory.CompanionTheory.MultiSeg.Rank.con_of_not_precedes {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {Γ Θ : ASeg T} {u : T} {j d : ℕ}
    (hΘ : Θ.start = s^[j + 1] u) (hu : u ∉ Θ.dec s) (hv : s^[d] u ∈ Θ.dec s)
    (hc : Con s u j (Γ.dec s)) (hn : ¬ APrecedes s Γ Θ) : Con s u d (Γ.dec s) := by sorry
