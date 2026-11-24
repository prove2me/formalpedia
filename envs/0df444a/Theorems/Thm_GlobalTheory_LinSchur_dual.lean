-- Prove2me | Theorems.Thm_GlobalTheory_LinSchur_dual
-- name    : GlobalTheory.LinSchur.dual
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:08:24.822889+00:00
-- url     : https://prove2.me/theorems/553f61d2-2270-418d-a41a-11a440757d76
-- title:
--   Lin Schur: dual
-- statement:
--   The Lin Schur construction uses the dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh.lean#L15-L25

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

theorem GlobalTheory.LinSchur.dual {k : Type} [Field k] [ValuativeRel k] {ψ0 : AddChar k ℂ} {n d : ℕ} {s : k}
    {Y : Matrix (Fin n) (Fin d) k} (hY : Y ∉ latt ψ0 n d s) :
    ∃ l : Matrix (Fin n) (Fin d) k →ₗ[k] k, (∀ Z ∈ latt ψ0 n d s, ψ0 (l Z) = 1) ∧ ψ0 (l Y) ≠ 1 := by sorry
