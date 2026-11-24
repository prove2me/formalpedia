-- Prove2me | Theorems.Thm_GlobalTheory_LinSchur_cind_mem
-- name    : GlobalTheory.LinSchur.cind_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:08:13.78589+00:00
-- url     : https://prove2.me/theorems/2fc88cbd-e271-4693-8061-31817a5f4e7e
-- title:
--   Lin Schur: cind mem
-- statement:
--   The Lin Schur construction uses the cind mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh.lean#L27-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh.lean#L27-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AddCharNegEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOpenSubgroupPeriodicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetEqSumAddCosetIndicatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharacterTrivialMatrixLatticeOpenCompactBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LinSchur

theorem GlobalTheory.LinSchur.cind_mem {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {L : AddSubgroup X}
    (ho : IsOpen (L : Set X)) (hc : IsCompact (L : Set X)) (y : X) : cind L y ∈ GlobalTheory.WeilM.SB X := by sorry
