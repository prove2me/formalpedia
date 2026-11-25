-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_locally_normal
-- name    : GlobalTheory.AnArc.locally_normal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:00:18.354046+00:00
-- url     : https://prove2.me/theorems/82d9c745-59d9-4bd2-b8c2-8cf3c72477b7
-- title:
--   An Arc: locally normal
-- statement:
--   The An Arc construction uses the locally normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L282-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L282-L292

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

theorem GlobalTheory.AnArc.locally_normal (hj : j ≠ 0) (h : th ∈ A.Theta j α) (p : ℂ × A.V) (hp : T₀ < p.1.im) :
    ∃ t ∈ 𝓝 p, ∃ u : A.X → ℝ, Summable u ∧ ∀ μ, ∀ q ∈ t,
      ‖A.term j α th μ q.2 * eTwoPi (q.1 * A.exponent j α μ)‖ ≤ u μ := by sorry
