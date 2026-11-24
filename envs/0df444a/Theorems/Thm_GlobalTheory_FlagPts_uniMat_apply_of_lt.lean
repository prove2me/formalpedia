-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_uniMat_apply_of_lt
-- name    : GlobalTheory.FlagPts.uniMat_apply_of_lt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:38:00.125713+00:00
-- url     : https://prove2.me/theorems/c5212629-6e0f-4514-bad1-486040b4d71a
-- title:
--   Flag Pts: uni Mat apply of lt
-- statement:
--   The Flag Pts construction uses the uni Mat apply of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UniMatBlockTriangular.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UniMatBlockTriangular.lean#L39-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
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
open Module TopologicalSpace
open GlobalTheory GlobalTheory.FlagPts
variable (k : Type) [Field k] {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable {k V}

theorem GlobalTheory.FlagPts.uniMat_apply_of_lt (u : AffPts k (CellIdx k V)) (i : ι) {a c : Fin (finrank k (V i))} (h : c < a) :
    uniMat u i a c = u ⟨i, (a, c), h⟩ := by sorry
