-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_le_awayLoc
-- name    : GlobalTheory.UTrans.le_awayLoc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:21:57.330441+00:00
-- url     : https://prove2.me/theorems/76205875-fa4f-44be-8746-238d5aa5f1cc
-- title:
--   UTrans: le away Loc
-- statement:
--   The UTrans construction uses the le away Loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUnitaryConjSplitLatticeOfLocal.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUnitaryConjSplitLatticeOfLocal.lean#L37-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidAdjustIntegralAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryEqQuasiReflectionMulTransvections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUnitaryConjSplitLatticeOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open GlobalTheory GlobalTheory.UTrans

theorem GlobalTheory.UTrans.le_awayLoc {V : Type} [AddCommGroup V] (L : AddSubgroup V) (b : ℕ) {v : V} (h : v ∈ L) :
    v ∈ awayLoc L b := by sorry
