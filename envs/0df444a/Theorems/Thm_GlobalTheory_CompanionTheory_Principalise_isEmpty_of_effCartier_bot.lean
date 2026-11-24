-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Principalise_isEmpty_of_effCartier_bot
-- name    : GlobalTheory.CompanionTheory.Principalise.isEmpty_of_effCartier_bot
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:58:56.119746+00:00
-- url     : https://prove2.me/theorems/d7795e96-8e61-436a-8ac3-da7560eb46ac
-- title:
--   Principalise: is Empty of eff Cartier bot
-- statement:
--   The Principalise construction uses the is Empty of eff Cartier bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIsoRestrictOfBlowupComp.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIsoRestrictOfBlowupComp.lean#L30-L37

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIsoRestrictOfBlowupComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Principalise

theorem GlobalTheory.CompanionTheory.Principalise.isEmpty_of_effCartier_bot {W : Scheme.{0}} (h : FinalTheorems.EffCartier (⊥ : W.IdealSheafData)) : IsEmpty W := by sorry
