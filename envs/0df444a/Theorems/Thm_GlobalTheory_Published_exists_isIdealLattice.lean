-- Prove2me | Theorems.Thm_GlobalTheory_Published_exists_isIdealLattice
-- name    : GlobalTheory.Published.exists_isIdealLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:41.829886+00:00
-- url     : https://prove2.me/theorems/6d548bbd-c076-4cf5-b8e0-b1345d44e579
-- title:
--   Published: exists is Ideal Lattice
-- statement:
--   The Published construction uses the exists is Ideal Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/ComplexMultiplicationJPremises.lean#L68-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/ComplexMultiplicationJPremises.lean#L68-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
open NumberField
open scoped nonZeroDivisors IntermediateField
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

theorem GlobalTheory.Published.exists_isIdealLattice [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ∃ L, _root_.GlobalTheory.Published.IsIdealLattice 𝔞 L := by sorry
