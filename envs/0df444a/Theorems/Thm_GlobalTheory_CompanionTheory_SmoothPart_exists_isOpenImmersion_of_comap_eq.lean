-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothPart_exists_isOpenImmersion_of_comap_eq
-- name    : GlobalTheory.CompanionTheory.SmoothPart.exists_isOpenImmersion_of_comap_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:52:42.442125+00:00
-- url     : https://prove2.me/theorems/29cfd604-47a9-43c7-ba90-e3362a91b5bf
-- title:
--   Smooth Part: exists is Open Immersion of comap eq
-- statement:
--   The Smooth Part construction uses the exists is Open Immersion of comap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/VanishingIdealSmoothAgreesOff.lean#L38-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/VanishingIdealSmoothAgreesOff.lean#L38-L58

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

theorem GlobalTheory.CompanionTheory.SmoothPart.exists_isOpenImmersion_of_comap_eq {X : Scheme.{0}} (I J : X.IdealSheafData) (O : X.Opens)
    (hO : (I.support : Set X) ⊆ O) (e : I.comap O.ι = J.comap O.ι) :
    ∃ h : I.subscheme ⟶ J.subscheme, IsOpenImmersion h ∧ h ≫ J.subschemeι = I.subschemeι := by sorry
