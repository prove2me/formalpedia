-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Fl_LogNorms_deg_const
-- name    : GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.deg_const
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:56.593985+00:00
-- url     : https://prove2.me/theorems/e5b7a16f-91a8-4dae-9851-0f24b2dcdb6d
-- title:
--   Log Norms: deg const
-- statement:
--   The Log Norms construction uses the deg const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/AdelicLattices/FactPrimes.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/AdelicLattices/FactPrimes.lean#L35-L38

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_AdelicLattices_FactPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open NumberField
open GlobalTheory.CompanionTheory.Ar.Fl.LogNorms
variable {k : Type} [Field k] [NumberField k]

theorem GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.deg_const (t : ℝ) : deg (⟨fun _ => t, fun _ _ => 0⟩ : LogNorms k) = -t := by sorry
