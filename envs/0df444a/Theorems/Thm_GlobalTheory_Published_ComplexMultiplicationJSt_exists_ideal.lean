-- Prove2me | Theorems.Thm_GlobalTheory_Published_ComplexMultiplicationJSt_exists_ideal
-- name    : GlobalTheory.Published.ComplexMultiplicationJSt.exists_ideal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:37:09.490369+00:00
-- url     : https://prove2.me/theorems/b51cf522-0878-4589-a6f6-f85be66ef6b2
-- title:
--   Complex Multiplication JSt: exists ideal
-- statement:
--   The Complex Multiplication JSt construction uses the exists ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/ComplexMultiplicationJPremises.lean#L146-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/ComplexMultiplicationJPremises.lean#L146-L164

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

theorem GlobalTheory.Published.ComplexMultiplicationJSt.exists_ideal
    (h : _root_.GlobalTheory.Published.ComplexMultiplicationJSt) [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (ρ : ℂ →ₐ[K] ℂ) :
    ∃ 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L L' : PeriodPair),
      _root_.GlobalTheory.Published.IsIdealLattice 𝔞 L → _root_.GlobalTheory.Published.IsIdealLattice (𝔟⁻¹ * 𝔞) L' →
        ρ (_root_.GlobalTheory.latticeCurve L).j = (_root_.GlobalTheory.latticeCurve L').j := by sorry
