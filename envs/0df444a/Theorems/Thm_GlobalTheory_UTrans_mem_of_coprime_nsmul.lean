-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_mem_of_coprime_nsmul
-- name    : GlobalTheory.UTrans.mem_of_coprime_nsmul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:24:10.063992+00:00
-- url     : https://prove2.me/theorems/56d58899-0278-489c-98a8-42a2c8a48032
-- title:
--   UTrans: mem of coprime nsmul
-- statement:
--   The UTrans construction uses the mem of coprime nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUnitaryConjSplitLatticeOfLocal.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUnitaryConjSplitLatticeOfLocal.lean#L24-L30

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

theorem GlobalTheory.UTrans.mem_of_coprime_nsmul {V : Type} [AddCommGroup V] (L : AddSubgroup V) {K M : ℕ} (h : K.Coprime M) {v : V}
    (h1 : K • v ∈ L) (h2 : M • v ∈ L) : v ∈ L := by sorry
