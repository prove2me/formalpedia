-- Prove2me | Theorems.Thm_GlobalTheory_T_isIso_restrict_of_blowup_comp
-- name    : GlobalTheory.T.isIso_restrict_of_blowup_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:01.196887+00:00
-- url     : https://prove2.me/theorems/4cc43b6b-67fb-544a-a8f9-dc7250b4faa1
-- title:
--   T: is Iso restrict of blowup comp
-- statement:
--   The T construction uses the is Iso restrict of blowup comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIsoRestrictOfBlowupCompStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIsoRestrictOfBlowupCompStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIsoRestrictOfBlowupComp
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIsoRestrictOfBlowupCompStatement
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

theorem GlobalTheory.T.isIso_restrict_of_blowup_comp : ∀ {X X₁ X₂ : Scheme.{0}} (s : X₁ ⟶ X) (π : X₂ ⟶ X₁) (Z : X₁.IdealSheafData) (V : X.Opens), IsIntegral X₁ → IsSeparated s → FinalTheorems.Blowup π Z → Nonempty X₂ → IsIso ((π ≫ s) ∣_ V) → IsIso (s ∣_ V) ∧ IsIso (π ∣_ (s ⁻¹ᵁ V)) := by sorry
