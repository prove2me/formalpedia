-- Prove2me | Theorems.Thm_GlobalTheory_T_lattice_dual_fourier_expansion_schwartz
-- name    : GlobalTheory.T.lattice_dual_fourier_expansion_schwartz
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:34:45.01663+00:00
-- url     : https://prove2.me/theorems/010143bb-93ed-469b-87f8-458f7041af41
-- title:
--   T: lattice dual fourier expansion schwartz
-- statement:
--   The T construction uses the lattice dual fourier expansion schwartz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeDualFourierExpansionSchwartzStatement.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeDualFourierExpansionSchwartzStatement.lean#L5-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeDualFourierExpansionSchwartz
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeDualFourierExpansionSchwartzStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lattice_dual_fourier_expansion_schwartz : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V), P.Nondegenerate →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : SchwartzMap V ℂ),
    ∃ c : V → ℂ, (∀ N : ℕ, Summable (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        ‖c μ‖ * (1 + ‖(μ : V)‖) ^ N)) ∧
      ∀ x : V, HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) (∑' l : Λ, f (x + l)) := by sorry
