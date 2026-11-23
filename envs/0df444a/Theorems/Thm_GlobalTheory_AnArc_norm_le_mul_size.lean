-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_norm_le_mul_size
-- name    : GlobalTheory.AnArc.norm_le_mul_size
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:00:02.344387+00:00
-- url     : https://prove2.me/theorems/a26465f8-d0cd-4afa-a730-57d698cc1804
-- title:
--   An Arc: norm le mul size
-- statement:
--   The An Arc construction uses the norm le mul size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HasSumLocallyUniformlyOnTerm.lean#L38-L46

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

theorem GlobalTheory.AnArc.norm_le_mul_size {E : Type*} [SeminormedAddCommGroup E] (f : A.X →+ E) {C : ℝ}
    (hC : ∀ i, ‖f (Module.Free.chooseBasis ℤ A.X i)‖ ≤ C) (μ : A.X) : ‖f μ‖ ≤ C * A.size μ := by sorry
