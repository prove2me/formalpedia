-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_nL_inv
-- name    : GlobalTheory.PrinTwo.nL_inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:55:45.709802+00:00
-- url     : https://prove2.me/theorems/38f86afe-5d0a-4262-b734-6ea661435582
-- title:
--   Prin Two: n L inv
-- statement:
--   The Prin Two construction uses the n L inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrincipalSeriesCoordinateNearInfinity.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrincipalSeriesCoordinateNearInfinity.lean#L12-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesCoordinateNearInfinity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped Topology
open GlobalTheory GlobalTheory.PrinTwo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.PrinTwo.nL_inv (x : k) : ((nL x)⁻¹ : GL (Fin (1 + 1)) k) = nL (-x) := by sorry
