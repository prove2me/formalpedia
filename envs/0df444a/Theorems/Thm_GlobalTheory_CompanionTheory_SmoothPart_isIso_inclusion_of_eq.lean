-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothPart_isIso_inclusion_of_eq
-- name    : GlobalTheory.CompanionTheory.SmoothPart.isIso_inclusion_of_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:53:13.966266+00:00
-- url     : https://prove2.me/theorems/9b5acd7b-1247-45cc-b64f-504a4d50177f
-- title:
--   Smooth Part: is Iso inclusion of eq
-- statement:
--   The Smooth Part construction uses the is Iso inclusion of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/VanishingIdealSmoothAgreesOff.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/VanishingIdealSmoothAgreesOff.lean#L32-L36

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

theorem GlobalTheory.CompanionTheory.SmoothPart.isIso_inclusion_of_eq {X : Scheme.{0}} {I J : X.IdealSheafData} (h : I ≤ J) (e : I = J) :
    IsIso (Scheme.IdealSheafData.inclusion h) := by sorry
