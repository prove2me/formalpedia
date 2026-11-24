-- Prove2me | Theorems.Thm_GlobalTheory_volume_mul_det_eq_one_of_unimodular
-- name    : GlobalTheory.volume_mul_det_eq_one_of_unimodular
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:24:56.586738+00:00
-- url     : https://prove2.me/theorems/6d9b36d3-57e1-4ef6-8280-50389da9c2a8
-- title:
--   Global Theory: volume mul det eq one of unimodular
-- statement:
--   The Global Theory construction uses the volume mul det eq one of unimodular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/VolumeFundamentalDomainStdRealBasis.lean#L79-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/VolumeFundamentalDomainStdRealBasis.lean#L79-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_VolumeFundamentalDomainStdRealBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder
open GlobalTheory
open UnimodVol

theorem GlobalTheory.volume_mul_det_eq_one_of_unimodular (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Fd : Set (Fin g → ℂ))
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hbij : Function.Bijective Ef)
    (hFd : IsAddFundamentalDomain Λ Fd volume) : (volume Fd).toReal * Hm.det.re = 1 := by sorry
