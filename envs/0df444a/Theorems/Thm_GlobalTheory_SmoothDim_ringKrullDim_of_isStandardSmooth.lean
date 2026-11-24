-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDim_ringKrullDim_of_isStandardSmooth
-- name    : GlobalTheory.SmoothDim.ringKrullDim_of_isStandardSmooth
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:16:05.914487+00:00
-- url     : https://prove2.me/theorems/9937f5c2-a086-46bb-80d7-7a2518eff861
-- title:
--   Smooth Dim: ring Krull Dim of is Standard Smooth
-- statement:
--   The Smooth Dim construction uses the ring Krull Dim of is Standard Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimOfEtaleMvPolynomial.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimOfEtaleMvPolynomial.lean#L52-L58

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

theorem GlobalTheory.SmoothDim.ringKrullDim_of_isStandardSmooth {K B : Type*} [CommRing K] (hK : IsField K) [CommRing B]
    [Nontrivial B] {g : ℕ} {f : K →+* B} (hf : f.IsStandardSmoothOfRelativeDimension g) :
    ringKrullDim B = g := by sorry
