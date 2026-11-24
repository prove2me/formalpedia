-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_CellCont_dual_mem_polyOnCell
-- name    : GlobalTheory.FlagPts.CellCont.dual_mem_polyOnCell
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:53:32.43884+00:00
-- url     : https://prove2.me/theorems/12a483be-f3d3-4853-8918-cadfb523e9bf
-- title:
--   Cell Cont: dual mem poly On Cell
-- statement:
--   The Cell Cont construction uses the dual mem poly On Cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousCellMap.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousCellMap.lean#L44-L49

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

theorem GlobalTheory.FlagPts.CellCont.dual_mem_polyOnCell (b : Frames k V) (i : ι) (φ : Dual k (V i)) (a : Fin (finrank k (V i))) :
    (fun b' : Frames k V => φ (b' i a)) ∈ polyOnCell b := by sorry
