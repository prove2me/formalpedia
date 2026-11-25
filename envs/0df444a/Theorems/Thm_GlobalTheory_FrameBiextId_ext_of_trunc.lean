-- Prove2me | Theorems.Thm_GlobalTheory_FrameBiextId_ext_of_trunc
-- name    : GlobalTheory.FrameBiextId.ext_of_trunc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:52.447805+00:00
-- url     : https://prove2.me/theorems/5350bff2-5596-43ae-8c40-474c6f0af77e
-- title:
--   Frame Biext Id: ext of trunc
-- statement:
--   The Frame Biext Id construction uses the ext of trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L151-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L151-L160

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FormalPointSubstitutionSeriesValueAtTwoPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}

theorem GlobalTheory.FrameBiextId.ext_of_trunc {R σ : Type} [CommRing R] [Finite σ] {f g : MvPowerSeries σ R}
    (h : ∀ m : ℕ, Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ (m + 1)) (truncTotal (m + 1) f) =
      Ideal.Quotient.mk _ (truncTotal (m + 1) g)) : f = g := by sorry
