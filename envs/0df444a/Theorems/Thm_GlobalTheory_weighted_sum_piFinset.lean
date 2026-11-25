-- Prove2me | Theorems.Thm_GlobalTheory_weighted_sum_piFinset
-- name    : GlobalTheory.weighted_sum_piFinset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:01.323803+00:00
-- url     : https://prove2.me/theorems/5273f5fa-4d71-42c9-a1d2-50cab07038b4
-- title:
--   Global Theory: weighted sum pi Finset
-- statement:
--   The Global Theory construction uses the weighted sum pi Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumPiFinsetFinSuccCons.lean#L58-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumPiFinsetFinSuccCons.lean#L58-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPiFinsetFinSuccCons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset

theorem GlobalTheory.weighted_sum_piFinset : ∀ (ι α K : Type) [Fintype ι] [DecidableEq ι] [CommRing K] (G : (α → K) → Prop) (S S' : Finset α) (w w' : K), (∀ f, G f → w * ∑ a ∈ S, f a = w' * ∑ a ∈ S', f a) → ∀ F : (ι → α) → K, (∀ (t : ι → α) (i : ι), G (fun a => F (Function.update t i a))) → w ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => S), F t = w' ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => S'), F t := by sorry
