-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_hasSumLocallyUniformlyOn_term
-- name    : GlobalTheory.AnArc.hasSumLocallyUniformlyOn_term
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:00:23.74467+00:00
-- url     : https://prove2.me/theorems/d293bf36-77f1-44a5-948e-3142d6f69dbc
-- title:
--   An Arc: has Sum Locally Uniformly On term
-- statement:
--   The An Arc construction uses the has Sum Locally Uniformly On term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L307-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L307-L310

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

theorem GlobalTheory.AnArc.hasSumLocallyUniformlyOn_term (hj : j ≠ 0) (h : th ∈ A.Theta j α) :
    HasSumLocallyUniformlyOn (fun μ (p : ℂ × A.V) => A.term j α th μ p.2 * eTwoPi (p.1 * A.exponent j α μ))
      (fun p => A.Sum j α th p.1 p.2) {p | T₀ < p.1.im} := by sorry
