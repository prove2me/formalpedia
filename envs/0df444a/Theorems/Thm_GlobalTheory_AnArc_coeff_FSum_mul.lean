-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_coeff_FSum_mul
-- name    : GlobalTheory.AnArc.coeff_FSum_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:56:51.112801+00:00
-- url     : https://prove2.me/theorems/21eea39a-613e-48cb-87c5-1c0a02c08da2
-- title:
--   An Arc: coeff FSum mul
-- statement:
--   The An Arc construction uses the coeff FSum mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L363-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L363-L367

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

theorem GlobalTheory.AnArc.coeff_FSum_mul (w : ℂ) (v : A.V) (n : ℤ) : (A.FSum j α th v).coeff n * eTwoPi w ^ n =
    ∑ μ ∈ A.level j α n, A.term j α th μ v * eTwoPi (w * A.exponent j α μ) := by sorry
