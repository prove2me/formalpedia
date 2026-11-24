-- Prove2me | Theorems.Thm_GlobalTheory_AbsDec_sum_proj
-- name    : GlobalTheory.AbsDec.sum_proj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:54:07.435323+00:00
-- url     : https://prove2.me/theorems/f616fb02-94ea-4583-ab27-cbac8143e3bb
-- title:
--   Abs Dec: sum proj
-- statement:
--   The Abs Dec construction uses the sum proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FixedVectorsIrreducibleSubrepDecomposition.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FixedVectorsIrreducibleSubrepDecomposition.lean#L43-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FixedVectorsIrreducibleSubrepDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule
open GlobalTheory GlobalTheory.AbsDec

theorem GlobalTheory.AbsDec.sum_proj {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι]
    [DecidableEq ι] (t : ι → Submodule ℂ V) (T : ι → V →ₗ[ℂ] V)
    (hT : ∀ i j, ∀ v ∈ t j, T i v = if i = j then v else 0) {v : V} (hv : v ∈ ⨆ i, t i) :
    ∑ i, T i v = v := by sorry
