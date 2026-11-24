-- Prove2me | Theorems.Thm_GlobalTheory_homogeneousComponent_mul_mem_span_degree
-- name    : GlobalTheory.homogeneousComponent_mul_mem_span_degree
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:55:41.532263+00:00
-- url     : https://prove2.me/theorems/80c1efa6-8d30-4cdf-b7e7-a537085585ee
-- title:
--   Global Theory: homogeneous Component mul mem span degree
-- statement:
--   The Global Theory construction uses the homogeneous Component mul mem span degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HomogeneousComponentMulMemSpanDegree.lean#L16-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HomogeneousComponentMulMemSpanDegree.lean#L16-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HomogeneousComponentMulMemSpanDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory
open MvPolynomial

theorem GlobalTheory.homogeneousComponent_mul_mem_span_degree {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) {d₀ d e : ℕ}
    (h₀ : d₀ ≤ d) (he : d ≤ e) {F : MvPolynomial σ K} (hF : F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d₀})
    (a : MvPolynomial σ K) :
    homogeneousComponent e (a * F) ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by sorry
