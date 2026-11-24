-- Prove2me | Theorems.Thm_GlobalTheory_MultiHilbert_component_mem_span_X
-- name    : GlobalTheory.MultiHilbert.component_mem_span_X
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:29:25.305793+00:00
-- url     : https://prove2.me/theorems/d3cc890e-88e5-4f27-9063-2fd72b72b54d
-- title:
--   Multi Hilbert: component mem span X
-- statement:
--   The Multi Hilbert construction uses the component mem span X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L207-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L207-L217

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {K σ M : Type} [Field K] [AddCancelCommMonoid M] (w : σ → M)

theorem GlobalTheory.MultiHilbert.component_mem_span_X (s : Set σ) (n : M) {G : MvPolynomial σ K}
    (hG : G ∈ Ideal.span (X '' s : Set (MvPolynomial σ K))) :
    weightedHomogeneousComponent w n G ∈ Ideal.span (X '' s : Set (MvPolynomial σ K)) := by sorry
