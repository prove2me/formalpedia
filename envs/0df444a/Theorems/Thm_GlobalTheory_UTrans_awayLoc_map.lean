-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_awayLoc_map
-- name    : GlobalTheory.UTrans.awayLoc_map
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:20:58.303967+00:00
-- url     : https://prove2.me/theorems/76e9538a-ed07-4082-8821-b8c035664221
-- title:
--   UTrans: away Loc map
-- statement:
--   The UTrans construction uses the away Loc map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUnitaryConjSplitLatticeOfLocal.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUnitaryConjSplitLatticeOfLocal.lean#L40-L44

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

theorem GlobalTheory.UTrans.awayLoc_map {V : Type} [AddCommGroup V] (L : AddSubgroup V) (b : ℕ) (f : V → V)
    (hf : ∀ (K : ℕ) v, f (K • v) = K • f v) (h : ∀ v ∈ L, f v ∈ awayLoc L b) :
    ∀ v ∈ awayLoc L b, f v ∈ awayLoc L b := by sorry
