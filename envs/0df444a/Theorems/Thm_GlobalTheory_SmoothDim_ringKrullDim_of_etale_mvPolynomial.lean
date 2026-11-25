-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDim_ringKrullDim_of_etale_mvPolynomial
-- name    : GlobalTheory.SmoothDim.ringKrullDim_of_etale_mvPolynomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:59:38.138015+00:00
-- url     : https://prove2.me/theorems/048a780b-8fa5-4e83-bae5-3fb750f60638
-- title:
--   Smooth Dim: ring Krull Dim of etale mv Polynomial
-- statement:
--   The Smooth Dim construction uses the ring Krull Dim of etale mv Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimOfEtaleMvPolynomial.lean#L21-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimOfEtaleMvPolynomial.lean#L21-L50

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

theorem GlobalTheory.SmoothDim.ringKrullDim_of_etale_mvPolynomial (K B : Type*) [Field K] [CommRing B] [Nontrivial B]
    (g : ℕ) [Algebra (MvPolynomial (Fin g) K) B] [Algebra.Etale (MvPolynomial (Fin g) K) B] :
    ringKrullDim B = g := by sorry
