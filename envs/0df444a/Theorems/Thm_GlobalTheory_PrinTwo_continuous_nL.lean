-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_continuous_nL
-- name    : GlobalTheory.PrinTwo.continuous_nL
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:55:28.492283+00:00
-- url     : https://prove2.me/theorems/e18a08df-ba30-4dd0-89c9-6b313296a61a
-- title:
--   Prin Two: continuous n L
-- statement:
--   The Prin Two construction uses the continuous n L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrincipalSeriesCoordinateNearInfinity.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrincipalSeriesCoordinateNearInfinity.lean#L16-L22

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

theorem GlobalTheory.PrinTwo.continuous_nL : Continuous (nL : k → GL (Fin (1 + 1)) k) := by sorry
