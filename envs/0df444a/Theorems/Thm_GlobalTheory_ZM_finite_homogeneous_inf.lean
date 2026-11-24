-- Prove2me | Theorems.Thm_GlobalTheory_ZM_finite_homogeneous_inf
-- name    : GlobalTheory.ZM.finite_homogeneous_inf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:03:10.006505+00:00
-- url     : https://prove2.me/theorems/a31eabca-408f-4360-86ad-d7613e9362d0
-- title:
--   ZM: finite homogeneous inf
-- statement:
--   The ZM construction uses the finite homogeneous inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/FiniteHomogeneousInf.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/FiniteHomogeneousInf.lean#L80-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_ExistsArBaseAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
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
noncomputable section
open GlobalTheory GlobalTheory.ZM
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g : ℕ} {J : Type}

theorem GlobalTheory.ZM.finite_homogeneous_inf {K σ : Type} [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    Module.Finite K ↥(MvPolynomial.homogeneousSubmodule σ K e ⊓ I.restrictScalars K) := by sorry
