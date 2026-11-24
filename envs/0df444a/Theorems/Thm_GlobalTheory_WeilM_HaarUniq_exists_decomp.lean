-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_HaarUniq_exists_decomp
-- name    : GlobalTheory.WeilM.HaarUniq.exists_decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:13.199896+00:00
-- url     : https://prove2.me/theorems/e6854087-1452-450c-bcff-99c5a23bfaf2
-- title:
--   Haar Uniq: exists decomp
-- statement:
--   The Haar Uniq construction uses the exists decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenAddSubgroup.lean#L78-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactOpenAddSubgroup.lean#L78-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.WeilM GlobalTheory.WeilM.HaarUniq
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
open MeasureTheory Filter Topology
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]

theorem GlobalTheory.WeilM.HaarUniq.exists_decomp [IsTopologicalAddGroup V] (K : OpenAddSubgroup V)
    {φ : V → ℂ} (hc : HasCompactSupport φ) (hinv : ∀ k ∈ K, ∀ x, φ (x + k) = φ x) :
    ∃ S : Finset (V ⧸ K.toAddSubgroup),
      φ = ∑ q ∈ S, φ q.out • (fun x => Set.indicator (K : Set V) (fun _ => (1 : ℂ)) (x + -q.out)) := by sorry
