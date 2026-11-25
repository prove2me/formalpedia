-- Prove2me | Theorems.Thm_GlobalTheory_periodisation_hasSum_fourier_bilinForm
-- name    : GlobalTheory.periodisation_hasSum_fourier_bilinForm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:34:51.602183+00:00
-- url     : https://prove2.me/theorems/358d533e-dc22-4ad6-a9f7-c85458c1b30f
-- title:
--   Global Theory: periodisation has Sum fourier bilin Form
-- statement:
--   The Global Theory construction uses the periodisation has Sum fourier bilin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeDualFourierExpansionSchwartz.lean#L34-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeDualFourierExpansionSchwartz.lean#L34-L101

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeDualFourierExpansionSchwartz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open scoped RealInnerProductSpace FourierTransform SchwartzMap
open GlobalTheory

theorem GlobalTheory.periodisation_hasSum_fourier_bilinForm {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V) (hP : P.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : SchwartzMap V ℂ) :
    ∃ c : V → ℂ, (∀ N : ℕ, Summable (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        ‖c μ‖ * (1 + ‖(μ : V)‖) ^ N)) ∧
      ∀ x : V, HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) (∑' l : Λ, f (x + l)) := by sorry
