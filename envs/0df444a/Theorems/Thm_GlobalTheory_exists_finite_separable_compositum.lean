-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_separable_compositum
-- name    : GlobalTheory.exists_finite_separable_compositum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:32.170809+00:00
-- url     : https://prove2.me/theorems/cd8a2b1b-fce7-4066-ac41-9340f9bbe223
-- title:
--   Global Theory: exists finite separable compositum
-- statement:
--   The Global Theory construction uses the exists finite separable compositum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFiniteSeparableCompositum.lean#L14-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFiniteSeparableCompositum.lean#L14-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteSeparableCompositum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory

theorem GlobalTheory.exists_finite_separable_compositum (K K' k : Type) [Field K] [Field K'] [Field k] [Algebra K k]
    [FiniteDimensional K k] [Algebra.IsSeparable K k] (φ : K →+* K') :
    ∃ (k' : Type) (_ : Field k') (_ : Algebra K' k') (g : k →+* k'), FiniteDimensional K' k' ∧
      Algebra.IsSeparable K' k' ∧ g.comp (algebraMap K k) = (algebraMap K' k').comp φ := by sorry
