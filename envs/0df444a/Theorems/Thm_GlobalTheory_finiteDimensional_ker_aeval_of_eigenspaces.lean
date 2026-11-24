-- Prove2me | Theorems.Thm_GlobalTheory_finiteDimensional_ker_aeval_of_eigenspaces
-- name    : GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:31.892533+00:00
-- url     : https://prove2.me/theorems/c4c5057c-c01d-438e-a7e8-0493ae0789a1
-- title:
--   Global Theory: finite Dimensional ker aeval of eigenspaces
-- statement:
--   The Global Theory construction uses the finite Dimensional ker aeval of eigenspaces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteDimensionalKerAevalOfEigenspaces.lean#L8-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteDimensionalKerAevalOfEigenspaces.lean#L8-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalKerAevalOfEigenspaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory

theorem GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces
    (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    (hT : ∀ lam : ℂ, FiniteDimensional ℂ (T.eigenspace lam)) (p : Polynomial ℂ) (hp : p ≠ 0) :
    FiniteDimensional ℂ (LinearMap.ker (Polynomial.aeval T p)) := by sorry
