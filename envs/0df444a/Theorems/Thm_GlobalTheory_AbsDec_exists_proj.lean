-- Prove2me | Theorems.Thm_GlobalTheory_AbsDec_exists_proj
-- name    : GlobalTheory.AbsDec.exists_proj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:52:13.213119+00:00
-- url     : https://prove2.me/theorems/78ce5e6d-6f80-4302-b394-33235374a062
-- title:
--   Abs Dec: exists proj
-- statement:
--   The Abs Dec construction uses the exists proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FixedVectorsIrreducibleSubrepDecomposition.lean#L7-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FixedVectorsIrreducibleSubrepDecomposition.lean#L7-L41

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

theorem GlobalTheory.AbsDec.exists_proj {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι]
    [DecidableEq ι] (t : ι → Submodule ℂ V) (ht : iSupIndep t) :
    ∃ T : ι → V →ₗ[ℂ] V, (∀ i v, T i v ∈ t i) ∧
      (∀ i j, ∀ v ∈ t j, T i v = if i = j then v else 0) := by sorry
