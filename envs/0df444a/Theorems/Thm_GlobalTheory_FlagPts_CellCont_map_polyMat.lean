-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_CellCont_map_polyMat
-- name    : GlobalTheory.FlagPts.CellCont.map_polyMat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:52:33.29189+00:00
-- url     : https://prove2.me/theorems/51f0752b-bd78-487d-8ef2-e0c4f7a9ca54
-- title:
--   Cell Cont: map poly Mat
-- statement:
--   The Cell Cont construction uses the map poly Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousCellMap.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousCellMap.lean#L19-L26

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

theorem GlobalTheory.FlagPts.CellCont.map_polyMat (u : AffPts k (CellIdx k V)) (i : ι) :
    (polyMat (k := k) (V := V) i).map (MvPolynomial.eval u) = uniMat u i := by sorry
