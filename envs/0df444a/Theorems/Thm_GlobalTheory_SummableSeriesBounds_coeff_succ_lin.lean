-- Prove2me | Theorems.Thm_GlobalTheory_SummableSeriesBounds_coeff_succ_lin
-- name    : GlobalTheory.SummableSeriesBounds.coeff_succ_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:07.362859+00:00
-- url     : https://prove2.me/theorems/01ee9314-fea6-4b6b-925c-4850974d0618
-- title:
--   Summable Series Bounds: coeff succ lin
-- statement:
--   The Summable Series Bounds construction uses the coeff succ lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L75-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableSeriesBounds
open PowerSeries Filter Topology
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
omit [IsUltrametricDist C]

theorem GlobalTheory.SummableSeriesBounds.coeff_succ_lin (π : C) (G : PowerSeries C) (n : ℕ) :
    coeff (n + 1) ((X - PowerSeries.C π) * G) = coeff n G - π * coeff (n + 1) G := by sorry
