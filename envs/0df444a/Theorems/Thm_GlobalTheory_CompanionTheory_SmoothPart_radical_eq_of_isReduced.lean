-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothPart_radical_eq_of_isReduced
-- name    : GlobalTheory.CompanionTheory.SmoothPart.radical_eq_of_isReduced
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:53:36.475816+00:00
-- url     : https://prove2.me/theorems/9ee6493d-7095-466d-a482-cb1857a88d28
-- title:
--   Smooth Part: radical eq of is Reduced
-- statement:
--   The Smooth Part construction uses the radical eq of is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/VanishingIdealSmoothAgreesOff.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/VanishingIdealSmoothAgreesOff.lean#L10-L19

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

theorem GlobalTheory.CompanionTheory.SmoothPart.radical_eq_of_isReduced {X : Scheme.{0}} (Z : X.IdealSheafData) [IsReduced Z.subscheme] :
    Z.radical = Z := by sorry
