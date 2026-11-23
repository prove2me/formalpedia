-- Prove2me | Theorems.Thm_GlobalTheory_hasSum_tuple_prod_exp
-- name    : GlobalTheory.hasSum_tuple_prod_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:08.992092+00:00
-- url     : https://prove2.me/theorems/7da1d124-769c-4dda-aa2d-7c84a35d10bd
-- title:
--   Global Theory: has Sum tuple prod exp
-- statement:
--   The Global Theory construction uses the has Sum tuple prod exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/LandauSummableOfExpDirichletSeriesEntire.lean#L46-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/LandauSummableOfExpDirichletSeriesEntire.lean#L46-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

theorem GlobalTheory.hasSum_tuple_prod_exp {ι : Type} (z : ι → ℂ) (g : ℂ) (h : HasSum z g) :
    HasSum (fun p : (Σ n : ℕ, Fin n → ι) => (∏ k, z (p.2 k)) / (p.1.factorial : ℂ))
      (Complex.exp g) := by sorry
