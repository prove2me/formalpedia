-- Prove2me | Theorems.Thm_GlobalTheory_Chow_exists_pow_mul_sub_rename_mem
-- name    : GlobalTheory.Chow.exists_pow_mul_sub_rename_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:35.422095+00:00
-- url     : https://prove2.me/theorems/5ab14aa6-054e-437e-8f7e-f4e32031bfe0
-- title:
--   Chow: exists pow mul sub rename mem
-- statement:
--   The Chow construction uses the exists pow mul sub rename mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L122-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L122-L159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {σ β : Type*} [Fintype σ]

theorem GlobalTheory.Chow.exists_pow_mul_sub_rename_mem {R : Type*} [CommRing R] (u : σ → R) (j : σ)
    (h : MvPolynomial (β × σ) R) :
    ∃ (m : ℕ) (g : MvPolynomial {v : β × σ // v ∉ elimIndices Set.univ j} R),
      h * C (u j ^ m) - rename Subtype.val g ∈ Ideal.span (Set.range (linForm u : β → _)) := by sorry
