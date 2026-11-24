-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_fderiv_coeff_FSum_eq_zero
-- name    : GlobalTheory.AnArc.fderiv_coeff_FSum_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:56:54.935222+00:00
-- url     : https://prove2.me/theorems/837f9cb6-22e9-4033-94e3-077c966e0ce8
-- title:
--   An Arc: fderiv coeff FSum eq zero
-- statement:
--   The An Arc construction uses the fderiv coeff FSum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L384-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L384-L386

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
variable {A} {T₀ : ℝ} (hT : A.IsConvLine T₀) {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ}
include hT
variable [NeZero j]
omit hT

theorem GlobalTheory.AnArc.fderiv_coeff_FSum_eq_zero {n : ℤ} (hn : n < -A.be α α) (v : A.V) :
    fderiv ℂ (fun v => (A.FSum j α th v).coeff n) v = 0 := by sorry
