-- Prove2me | Theorems.Thm_GlobalTheory_AbsDec_proj_comm
-- name    : GlobalTheory.AbsDec.proj_comm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:52:32.462154+00:00
-- url     : https://prove2.me/theorems/f8dbac00-249c-4029-b522-713fa9a28b02
-- title:
--   Abs Dec: proj comm
-- statement:
--   The Abs Dec construction uses the proj comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FixedVectorsIrreducibleSubrepDecomposition.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FixedVectorsIrreducibleSubrepDecomposition.lean#L52-L62

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

theorem GlobalTheory.AbsDec.proj_comm {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ι → Submodule ℂ V) (T : ι → V →ₗ[ℂ] V)
    (hT : ∀ i j, ∀ v ∈ t j, T i v = if i = j then v else 0)
    (hst : ∀ j g, ∀ v ∈ t j, ρ g v ∈ t j) (i : ι) (g : G) {v : V} (hv : v ∈ ⨆ j, t j) :
    T i (ρ g v) = ρ g (T i v) := by sorry
