-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_awayLoc_of_nsmul
-- name    : GlobalTheory.UTrans.awayLoc_of_nsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:01.925496+00:00
-- url     : https://prove2.me/theorems/89755215-c2f8-405c-8662-92a86787fcef
-- title:
--   UTrans: away Loc of nsmul
-- statement:
--   The UTrans construction uses the away Loc of nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUnitaryConjSplitLatticeOfLocal.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUnitaryConjSplitLatticeOfLocal.lean#L32-L35

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

theorem GlobalTheory.UTrans.awayLoc_of_nsmul {V : Type} [AddCommGroup V] (L : AddSubgroup V) {b K : ℕ} (hK : K.Coprime b) {v : V}
    (h : K • v ∈ awayLoc L b) : v ∈ awayLoc L b := by sorry
