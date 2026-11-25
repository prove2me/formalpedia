-- Prove2me | Theorems.Thm_GlobalTheory_T_vanishing_ideal_smooth_agrees_off
-- name    : GlobalTheory.T.vanishing_ideal_smooth_agrees_off
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:08:42.11592+00:00
-- url     : https://prove2.me/theorems/f8a0196c-680f-4b1b-b8bd-5d519b566574
-- title:
--   T: vanishing ideal smooth agrees off
-- statement:
--   The T construction uses the vanishing ideal smooth agrees off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/VanishingIdealSmoothAgreesOffStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/VanishingIdealSmoothAgreesOffStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_VanishingIdealSmoothAgreesOff
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_VanishingIdealSmoothAgreesOffStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.vanishing_ideal_smooth_agrees_off : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData) (A : Closeds X) (O : X.Opens), Smooth (Z.subschemeι ≫ g) → (A : Set X) ⊆ Z.support → (O : Set X) = ((Z.support : Set X) \ A)ᶜ → Smooth ((Scheme.IdealSheafData.vanishingIdeal A).subschemeι ≫ g) ∧ (Scheme.IdealSheafData.vanishingIdeal A).comap O.ι = Z.comap O.ι := by sorry
