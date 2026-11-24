-- Prove2me | Theorems.Thm_GlobalTheory_NormEq_Cmpl_ball_mem_nhds_of_ne
-- name    : GlobalTheory.NormEq.Cmpl.ball_mem_nhds_of_ne
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:34:25.917611+00:00
-- url     : https://prove2.me/theorems/3f5d9584-23b6-44f8-ad0b-61ec0e6cdd5c
-- title:
--   Cmpl: ball mem nhds of ne
-- statement:
--   The Cmpl construction uses the ball mem nhds of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormFiltrationComplete.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormFiltrationComplete.lean#L26-L29

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFiltrationComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.NormEq GlobalTheory.NormEq.Cmpl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.NormEq.Cmpl.ball_mem_nhds_of_ne {x c : L} (hc : c ≠ 0) : {y | Valued.v (y - x) < Valued.v c} ∈ 𝓝 x := by sorry
