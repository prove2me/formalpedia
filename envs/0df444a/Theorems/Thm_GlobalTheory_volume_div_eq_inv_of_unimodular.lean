-- Prove2me | Theorems.Thm_GlobalTheory_volume_div_eq_inv_of_unimodular
-- name    : GlobalTheory.volume_div_eq_inv_of_unimodular
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:51:48.801289+00:00
-- url     : https://prove2.me/theorems/ab7f68c0-adfb-4318-8fac-f9e287324a79
-- title:
--   Global Theory: volume div eq inv of unimodular
-- statement:
--   The Global Theory construction uses the volume div eq inv of unimodular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/VolumeFundamentalDomainStdRealBasis.lean#L122-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/VolumeFundamentalDomainStdRealBasis.lean#L122-L143

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

theorem GlobalTheory.volume_div_eq_inv_of_unimodular (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Fd : Set (Fin g → ℂ))
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hbij : Function.Bijective Ef)
    (hFd : IsAddFundamentalDomain Λ Fd volume) (W : Matrix (Fin g) (Fin g) ℂ) (hW : W.det ≠ 0) :
    0 < Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2 ∧
    (volume Fd).toReal / (Real.pi ^ g * ‖W.det‖ ^ 2) = (Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2)⁻¹ ∧
    (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W i) (W j)).det =
      ((Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2 : ℝ) : ℂ) := by sorry
