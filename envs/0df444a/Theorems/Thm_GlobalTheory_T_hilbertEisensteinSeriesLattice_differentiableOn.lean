-- Prove2me | Theorems.Thm_GlobalTheory_T_hilbertEisensteinSeriesLattice_differentiableOn
-- name    : GlobalTheory.T.hilbertEisensteinSeriesLattice_differentiableOn
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:33:08.431407+00:00
-- url     : https://prove2.me/theorems/27fc6117-f797-5e47-88c0-30b883597ab4
-- title:
--   T: hilbert Eisenstein Series Lattice differentiable On
-- statement:
--   The T construction uses the hilbert Eisenstein Series Lattice differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinSeriesLatticeDifferentiableOnStatement.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinSeriesLatticeDifferentiableOnStatement.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesLatticeDifferentiableOn
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesLatticeDifferentiableOnStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hilbertEisensteinSeriesLattice_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ),
  (∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z)) →
  DifferentiableOn ℂ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisSum 𝔞 𝔟 k 0) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by sorry
