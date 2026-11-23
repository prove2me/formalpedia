-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_term_add_index
-- name    : GlobalTheory.AnArc.term_add_index
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:13:34.089212+00:00
-- url     : https://prove2.me/theorems/c421da36-75ca-4c19-84fc-accaa5aaf5ea
-- title:
--   An Arc: term add index
-- statement:
--   The An Arc construction uses the term add index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L230-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L230-L237

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.term_add_index (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (μ y : A.X) (v : A.V) :
    A.term j α th (μ + y) v =
      (A.psi y : ℂ) ^ j * eTwoPi (A.T y α) * A.term j (α + j • y) (fun z => th (z + A.ct y)) μ v := by sorry
