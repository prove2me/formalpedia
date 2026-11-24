-- Prove2me | Theorems.Thm_GlobalTheory_latFinOrdSt
-- name    : GlobalTheory.latFinOrdSt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:03:15.977132+00:00
-- url     : https://prove2.me/theorems/b27ec8ba-3e3b-4441-a124-30165b7fb7d4
-- title:
--   Global Theory: lat Fin Ord St
-- statement:
--   The Global Theory construction uses the lat Fin Ord St property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsPowEqOneOfPosDefForm.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsPowEqOneOfPosDefForm.lean#L52-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsPowEqOneOfPosDefForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.latFinOrdSt : ReciprocityTheory.ChartRestriction.G.Geo.Tor.LatFinOrdSt := by sorry
