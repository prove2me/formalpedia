-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDim_ringKrullDim_eq_of_span_eq_top
-- name    : GlobalTheory.SmoothDim.ringKrullDim_eq_of_span_eq_top
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:16:16.545422+00:00
-- url     : https://prove2.me/theorems/c19b20ac-1773-4409-8b69-ada926684188
-- title:
--   Smooth Dim: ring Krull Dim eq of span eq top
-- statement:
--   The Smooth Dim construction uses the ring Krull Dim eq of span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimOfEtaleMvPolynomial.lean#L60-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RingKrullDimOfEtaleMvPolynomial.lean#L60-L91

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

theorem GlobalTheory.SmoothDim.ringKrullDim_eq_of_span_eq_top {A : Type*} [CommRing A] [Nontrivial A] (s : Set A)
    (hs : Ideal.span s = ⊤) (d : WithBot ℕ∞)
    (h : ∀ t ∈ s, Nontrivial (Localization.Away t) → ringKrullDim (Localization.Away t) = d) :
    ringKrullDim A = d := by sorry
