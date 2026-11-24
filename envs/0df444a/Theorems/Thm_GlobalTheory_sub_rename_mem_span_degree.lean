-- Prove2me | Theorems.Thm_GlobalTheory_sub_rename_mem_span_degree
-- name    : GlobalTheory.sub_rename_mem_span_degree
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:22:24.776892+00:00
-- url     : https://prove2.me/theorems/5ec56f4d-797d-4d79-bf9f-7c9fb0190668
-- title:
--   Global Theory: sub rename mem span degree
-- statement:
--   The Global Theory construction uses the sub rename mem span degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FinrankMapAddFinrankInfKerOfFinite.lean#L30-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FinrankMapAddFinrankInfKerOfFinite.lean#L30-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPolynomialFinrankHomogeneousSubmoduleStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FinrankMapAddFinrankInfKerOfFinite
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
open GlobalTheory
open MvPolynomial

theorem GlobalTheory.sub_rename_mem_span_degree {K σ : Type*} [Field K] (t : σ → σ)
    (I : Ideal (MvPolynomial σ K)) (hI : ∀ F, F - rename t F ∈ I) {d : ℕ} (hd : 1 ≤ d)
    {e : ℕ} (he : d ≤ e) : ∀ F : MvPolynomial σ K, F.IsHomogeneous e →
      F - rename t F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by sorry
