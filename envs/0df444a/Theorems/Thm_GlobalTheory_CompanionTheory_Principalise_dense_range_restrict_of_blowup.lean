-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Principalise_dense_range_restrict_of_blowup
-- name    : GlobalTheory.CompanionTheory.Principalise.dense_range_restrict_of_blowup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:59:22.132622+00:00
-- url     : https://prove2.me/theorems/7330b51e-c953-4c81-9642-959921c9374c
-- title:
--   Principalise: dense range restrict of blowup
-- statement:
--   The Principalise construction uses the dense range restrict of blowup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIsoRestrictOfBlowupComp.lean#L39-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIsoRestrictOfBlowupComp.lean#L39-L58

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

theorem GlobalTheory.CompanionTheory.Principalise.dense_range_restrict_of_blowup {X₁ X₂ : Scheme.{0}} [IsIntegral X₁] [Nonempty X₂] {π : X₂ ⟶ X₁}
    {Z : X₁.IdealSheafData} (hB : FinalTheorems.Blowup π Z) (U : X₁.Opens) : Dense (Set.range (π ∣_ U)) := by sorry
