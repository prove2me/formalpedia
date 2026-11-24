-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_LogSqVar_first_variation
-- name    : GlobalTheory.ClassFin.LogSqVar.first_variation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:38.515806+00:00
-- url     : https://prove2.me/theorems/f634829e-42a6-4519-be9e-b69ba6830e1c
-- title:
--   Log Sq Var: first variation
-- statement:
--   The Log Sq Var construction uses the first variation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HermitianLogTraceSqFirstVariationBound.lean#L163-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HermitianLogTraceSqFirstVariationBound.lean#L163-L293

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LogSqLeTangentAddSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HermitianLogTraceSqFirstVariationBound
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
open GlobalTheory GlobalTheory.ClassFin GlobalTheory.ClassFin.LogSqVar
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open Matrix

theorem GlobalTheory.ClassFin.LogSqVar.first_variation (ι : Type) [Fintype ι] [DecidableEq ι]
    (H A : Matrix ι ι ℂ) :
    _root_.GlobalTheory.ClassFin.IsLog H A →
      ∃ (C : ℝ) (δ : ℝ), (0 : ℝ) < δ ∧
        ∀ (Y H' : Matrix ι ι ℂ), (∀ (i j : ι), ‖Y i j‖ ≤ δ) →
          _root_.GlobalTheory.ClassFin.IsLog H' (A + Y) →
            Complex.re (Matrix.trace (H' * H')) ≤
              Complex.re (Matrix.trace (H * H)) + (2 : ℝ) * Complex.re (Matrix.trace (H * A⁻¹ * Y)) +
                C * ∑ i : ι, ∑ j : ι, ‖Y i j‖ ^ (2 : ℕ) := by sorry
