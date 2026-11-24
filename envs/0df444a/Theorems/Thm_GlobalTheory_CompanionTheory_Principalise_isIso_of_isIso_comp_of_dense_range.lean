-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Principalise_isIso_of_isIso_comp_of_dense_range
-- name    : GlobalTheory.CompanionTheory.Principalise.isIso_of_isIso_comp_of_dense_range
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:58:54.711348+00:00
-- url     : https://prove2.me/theorems/0346db06-3b0e-4a29-9b7c-e98281ddf283
-- title:
--   Principalise: is Iso of is Iso comp of dense range
-- statement:
--   The Principalise construction uses the is Iso of is Iso comp of dense range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIsoRestrictOfBlowupComp.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIsoRestrictOfBlowupComp.lean#L11-L28

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

theorem GlobalTheory.CompanionTheory.Principalise.isIso_of_isIso_comp_of_dense_range {A P V : Scheme.{0}} (a : A ⟶ P) (b : P ⟶ V) [IsIso (a ≫ b)]
    [IsSeparated b] [IsReduced P] (hd : Dense (Set.range a)) : IsIso b ∧ IsIso a := by sorry
