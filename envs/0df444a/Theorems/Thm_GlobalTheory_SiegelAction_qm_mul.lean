-- Prove2me | Theorems.Thm_GlobalTheory_SiegelAction_qm_mul
-- name    : GlobalTheory.SiegelAction.qm_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:41.655806+00:00
-- url     : https://prove2.me/theorems/bbff76aa-7ac8-4dc1-aeb7-61249d8ecc40
-- title:
--   Siegel Action: qm mul
-- statement:
--   The Siegel Action construction uses the qm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SymplecticSiegelActionMemUpperHalfSpaceAndCocycl.lean#L156-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SymplecticSiegelActionMemUpperHalfSpaceAndCocycl.lean#L156-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SiegelAction
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.SiegelAction.qm_mul {α β γ : Type} [Fintype β] (A : Matrix α β ℚ) (B : Matrix β γ ℚ) :
    qm (A * B) = qm A * qm B := by sorry
