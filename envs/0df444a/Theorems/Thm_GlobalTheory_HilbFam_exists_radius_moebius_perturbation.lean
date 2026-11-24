-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_exists_radius_moebius_perturbation
-- name    : GlobalTheory.HilbFam.exists_radius_moebius_perturbation
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:20:38.457751+00:00
-- url     : https://prove2.me/theorems/a2d84bcd-b335-4c34-87ec-f26cd9029004
-- title:
--   Hilb Fam: exists radius moebius perturbation
-- statement:
--   The Hilb Fam construction uses the exists radius moebius perturbation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRadiusMoebiusPerturbationUpperHalfPlane.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRadiusMoebiusPerturbationUpperHalfPlane.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRadiusMoebiusPerturbationUpperHalfPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HilbFam

theorem GlobalTheory.HilbFam.exists_radius_moebius_perturbation :
    ∀ (τ c t : ℂ), 0 < τ.im → ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      1 / 2 ≤ ‖1 + z * c‖ ∧ τ.im / 2 ≤ (τ + t * z / (1 + z * c)).im := by sorry
