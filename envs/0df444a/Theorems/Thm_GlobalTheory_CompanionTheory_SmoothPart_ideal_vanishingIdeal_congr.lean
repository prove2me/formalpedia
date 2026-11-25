-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothPart_ideal_vanishingIdeal_congr
-- name    : GlobalTheory.CompanionTheory.SmoothPart.ideal_vanishingIdeal_congr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:53:01.490509+00:00
-- url     : https://prove2.me/theorems/71e1d032-3759-4c3f-8e5f-f01d642e56d8
-- title:
--   Smooth Part: ideal vanishing Ideal congr
-- statement:
--   The Smooth Part construction uses the ideal vanishing Ideal congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/VanishingIdealSmoothAgreesOff.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/VanishingIdealSmoothAgreesOff.lean#L21-L30

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

theorem GlobalTheory.CompanionTheory.SmoothPart.ideal_vanishingIdeal_congr {X : Scheme.{0}} (A B : Closeds X) (W : X.affineOpens)
    (h : ∀ x ∈ W.1, x ∈ A ↔ x ∈ B) :
    (Scheme.IdealSheafData.vanishingIdeal A).ideal W =
      (Scheme.IdealSheafData.vanishingIdeal B).ideal W := by sorry
