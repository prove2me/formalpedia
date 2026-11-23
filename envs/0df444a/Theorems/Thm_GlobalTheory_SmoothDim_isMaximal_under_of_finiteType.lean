-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDim_isMaximal_under_of_finiteType
-- name    : GlobalTheory.SmoothDim.isMaximal_under_of_finiteType
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:42.344709+00:00
-- url     : https://prove2.me/theorems/edfccf61-45eb-48a6-8490-bedf1bd779ef
-- title:
--   Smooth Dim: is Maximal under of finite Type
-- statement:
--   The Smooth Dim construction uses the is Maximal under of finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimOfEtaleMvPolynomial.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimOfEtaleMvPolynomial.lean#L11-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SmoothDim

theorem GlobalTheory.SmoothDim.isMaximal_under_of_finiteType (K R B : Type*) [Field K] [CommRing R] [CommRing B]
    [Algebra K R] [Algebra K B] [Algebra R B] [IsScalarTower K R B] [Algebra.FiniteType K B]
    (m : Ideal B) [m.IsMaximal] : (m.under R).IsMaximal := by sorry
