-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_HermiteReduction_exists_reduced
-- name    : GlobalTheory.ClassFin.HermiteReduction.exists_reduced
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:11:34.99454+00:00
-- url     : https://prove2.me/theorems/a5bba9f4-4e21-40ab-9255-33fab697b31a
-- title:
--   Hermite Reduction: exists reduced
-- statement:
--   The Hermite Reduction construction uses the exists reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsHermiteReducedLatticeBasis.lean#L111-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsHermiteReducedLatticeBasis.lean#L111-L166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IwasawaDecompositionRealMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DetLeadingMinorGramIwasawaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramLeadingMinorLowerBoundIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnipotentUpperSizeReductionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramMinorSwapAdjacentColumnsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsHermiteReducedLatticeBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin GlobalTheory.ClassFin.HermiteReduction

theorem GlobalTheory.ClassFin.HermiteReduction.exists_reduced : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ (γ : Matrix (Fin N) (Fin N) ℤ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), (γ.det = 1 ∨ γ.det = -1) ∧ kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧ (∀ i j, j < i → n i j = 0) ∧ (∀ i j, i < j → |n i j| ≤ 1 / 2) ∧ (∀ p q : Fin N, (q : ℕ) = p + 1 → a p ≤ 2 * a q) ∧ g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by sorry
