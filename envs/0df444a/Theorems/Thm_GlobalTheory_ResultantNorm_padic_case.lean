-- Prove2me | Theorems.Thm_GlobalTheory_ResultantNorm_padic_case
-- name    : GlobalTheory.ResultantNorm.padic_case
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:21:12.33457+00:00
-- url     : https://prove2.me/theorems/d95b2b12-2034-41fa-aa3d-36dabfaa025d
-- title:
--   Resultant Norm: padic case
-- statement:
--   The Resultant Norm construction uses the padic case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEq.lean#L186-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEq.lean#L186-L209

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEq
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
open GlobalTheory.ResultantNorm
open Polynomial Filter Topology
variable {l : ℕ} [Fact l.Prime] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

theorem GlobalTheory.ResultantNorm.padic_case (a b : Multiset Ω)
    (h : ∀ F : ℤ[X], ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖)
    (F : ℚ_[l][X]) :
    ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖ := by sorry
