-- Prove2me | Theorems.Thm_GlobalTheory_exists_testFunctions_subset_of_mem_nhds
-- name    : GlobalTheory.exists_testFunctions_subset_of_mem_nhds
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:42:43.282336+00:00
-- url     : https://prove2.me/theorems/23593b94-0107-48e1-8554-b4128a8549ab
-- title:
--   Global Theory: exists test Functions subset of mem nhds
-- statement:
--   The Global Theory construction uses the exists test Functions subset of mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsTestFunctionsSubsetOfMemNhds.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsTestFunctionsSubsetOfMemNhds.lean#L11-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open AffinePoints

theorem GlobalTheory.exists_testFunctions_subset_of_mem_nhds {A : Type*} [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] {e : A →ₐ[ℂ] ℂ} {U : Set (A →ₐ[ℂ] ℂ)} (hU : U ∈ 𝓝 e) :
    ∃ (n : ℕ) (f : Fin n → A) (ε : ℝ), 0 < ε ∧
      ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → x ∈ U := by sorry
