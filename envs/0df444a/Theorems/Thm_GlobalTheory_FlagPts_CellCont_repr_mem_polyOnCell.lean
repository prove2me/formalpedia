-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_CellCont_repr_mem_polyOnCell
-- name    : GlobalTheory.FlagPts.CellCont.repr_mem_polyOnCell
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:53:47.253442+00:00
-- url     : https://prove2.me/theorems/efcfbb5e-803b-4f6d-8c3a-56fe2a787459
-- title:
--   Cell Cont: repr mem poly On Cell
-- statement:
--   The Cell Cont construction uses the repr mem poly On Cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousCellMap.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousCellMap.lean#L65-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousCellMap
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
open Module TopologicalSpace GlobalTheory.FlagPts
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.CellCont
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

theorem GlobalTheory.FlagPts.CellCont.repr_mem_polyOnCell (b : Frames k V) (i : ι) (v : V i) (a : Fin (finrank k (V i))) :
    (fun b' : Frames k V => (b' i).repr v a) ∈ polyOnCell b := by sorry
