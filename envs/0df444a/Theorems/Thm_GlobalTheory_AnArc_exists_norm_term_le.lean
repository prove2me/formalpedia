-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_exists_norm_term_le
-- name    : GlobalTheory.AnArc.exists_norm_term_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:57:21.59188+00:00
-- url     : https://prove2.me/theorems/c9f55a8e-1501-45b5-b4e8-0b9922374164
-- title:
--   An Arc: exists norm term le
-- statement:
--   The An Arc construction uses the exists norm term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L212-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L212-L273

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

theorem GlobalTheory.AnArc.exists_norm_term_le (hj : j ≠ 0) (h : th ∈ A.Theta j α) {T₁ : ℝ} (h₁ : T₀ ≤ T₁) (R : ℝ) :
    ∃ K D : ℝ, ∀ μ (w : ℂ) (v : A.V), T₁ ≤ w.im → |w.im| ≤ R → ‖v‖ ≤ R →
      ‖A.term j α th μ v * eTwoPi (w * A.exponent j α μ)‖ ≤
        K * Real.exp (-(Real.pi * (T₁ - T₀) * A.be μ μ) + D * A.size μ) := by sorry
