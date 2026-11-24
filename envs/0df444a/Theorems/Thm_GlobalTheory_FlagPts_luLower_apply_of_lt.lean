-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_luLower_apply_of_lt
-- name    : GlobalTheory.FlagPts.luLower_apply_of_lt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:54:15.837399+00:00
-- url     : https://prove2.me/theorems/fd517f4b-e1aa-4534-b840-c0109fbd82e0
-- title:
--   Flag Pts: lu Lower apply of lt
-- statement:
--   The Flag Pts construction uses the lu Lower apply of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LuLowerLowerTriangular.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LuLowerLowerTriangular.lean#L27-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LuLowerLowerTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts
variable {k : Type} [Field k] {n : ℕ}

theorem GlobalTheory.FlagPts.luLower_apply_of_lt (P : Matrix (Fin n) (Fin n) k) {a m : Fin n} (h : m < a) :
    luLower P a m = luNum P a m / leadMinor P m := by sorry
