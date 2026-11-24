-- Prove2me | Theorems.Thm_GlobalTheory_MultiHilbert_component_mem_colonX
-- name    : GlobalTheory.MultiHilbert.component_mem_colonX
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:29:39.107799+00:00
-- url     : https://prove2.me/theorems/cd9d46ad-b542-4a5d-b82c-2bfc8197e6e0
-- title:
--   Multi Hilbert: component mem colon X
-- statement:
--   The Multi Hilbert construction uses the component mem colon X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L228-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L228-L233

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

theorem GlobalTheory.MultiHilbert.component_mem_colonX {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ n, weightedHomogeneousComponent w n F ∈ I) (i : σ) :
    ∀ F ∈ colonX I i, ∀ n, weightedHomogeneousComponent w n F ∈ colonX I i := by sorry
