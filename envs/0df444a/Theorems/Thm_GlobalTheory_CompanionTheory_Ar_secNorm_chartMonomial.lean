-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_secNorm_chartMonomial
-- name    : GlobalTheory.CompanionTheory.Ar.secNorm_chartMonomial
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:53.79635+00:00
-- url     : https://prove2.me/theorems/ce6f1804-37b9-5ec2-9f03-a829aa9071c8
-- title:
--   Ar: sec Norm chart Monomial
-- statement:
--   The Ar construction uses the sec Norm chart Monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/HodgeIPIffHodgeFormConj.lean#L278-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/HodgeIPIffHodgeFormConj.lean#L278-L287

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
variable {z : Spec (CommRingCat.of ℂ) ⟶ X}
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {A : HermLine J} {e₀ : Ω}
  {w : (Σ k, J k) → ℂ} {t : Ω} {ν ν' : ℝ}

theorem GlobalTheory.CompanionTheory.Ar.secNorm_chartMonomial (hz : genPt ξ ⤳ centre z) (he : e₀ ≠ 0) (hw : CoordsAt ξ y z w) (c : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    SecNorm ξ y A e₀ z w ((∏ k, y ⟨k, c k⟩ ^ A.a k) * e₀) ((∏ k, ‖w ⟨k, c k⟩‖ ^ A.a k) / A.h w) := by sorry
