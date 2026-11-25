-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothPart_smooth_and_comap_eq
-- name    : GlobalTheory.CompanionTheory.SmoothPart.smooth_and_comap_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:52:21.440833+00:00
-- url     : https://prove2.me/theorems/96abc0da-bd3b-4af5-86e1-7c95762a6826
-- title:
--   Smooth Part: smooth and comap eq
-- statement:
--   The Smooth Part construction uses the smooth and comap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/VanishingIdealSmoothAgreesOff.lean#L60-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/VanishingIdealSmoothAgreesOff.lean#L60-L91

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_VanishingIdealSmoothAgreesOff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothPart

theorem GlobalTheory.CompanionTheory.SmoothPart.smooth_and_comap_eq : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData)
    (A : Closeds X) (O : X.Opens), Smooth (Z.subschemeι ≫ g) → (A : Set X) ⊆ Z.support →
    (O : Set X) = ((Z.support : Set X) \ A)ᶜ →
    Smooth ((Scheme.IdealSheafData.vanishingIdeal A).subschemeι ≫ g) ∧
      (Scheme.IdealSheafData.vanishingIdeal A).comap O.ι = Z.comap O.ι := by sorry
