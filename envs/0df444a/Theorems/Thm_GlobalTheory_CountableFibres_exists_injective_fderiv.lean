-- Prove2me | Theorems.Thm_GlobalTheory_CountableFibres_exists_injective_fderiv
-- name    : GlobalTheory.CountableFibres.exists_injective_fderiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:53.499687+00:00
-- url     : https://prove2.me/theorems/5ec9a80d-8423-4623-9c28-adca3a1847d0
-- title:
--   Countable Fibres: exists injective fderiv
-- statement:
--   The Countable Fibres construction uses the exists injective fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MvPolynomialEqZeroOfEventually.lean#L14-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MvPolynomialEqZeroOfEventually.lean#L14-L164

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialEqZeroOfEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CountableFibres
open Filter Topology

theorem GlobalTheory.CountableFibres.exists_injective_fderiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) {f : E → F}
    (hf : ∀ z ∈ U, ContDiffAt ℂ 1 f z) (hc : ∀ z ∈ U, {z' ∈ U | f z' = f z}.Countable) :
    ∃ z ∈ U, Function.Injective (fderiv ℂ f z) := by sorry
