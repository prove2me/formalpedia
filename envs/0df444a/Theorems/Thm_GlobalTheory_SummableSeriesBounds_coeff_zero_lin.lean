-- Prove2me | Theorems.Thm_GlobalTheory_SummableSeriesBounds_coeff_zero_lin
-- name    : GlobalTheory.SummableSeriesBounds.coeff_zero_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:30.201512+00:00
-- url     : https://prove2.me/theorems/b0f62e45-c70f-4398-9e61-a4a14ebcbfae
-- title:
--   Summable Series Bounds: coeff zero lin
-- statement:
--   The Summable Series Bounds construction uses the coeff zero lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean#L69-L72

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

theorem GlobalTheory.SummableSeriesBounds.coeff_zero_lin (π : C) (G : PowerSeries C) :
    coeff 0 ((X - PowerSeries.C π) * G) = -(π * coeff 0 G) := by sorry
