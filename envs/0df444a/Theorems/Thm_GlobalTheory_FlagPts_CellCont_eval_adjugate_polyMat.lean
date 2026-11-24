-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_CellCont_eval_adjugate_polyMat
-- name    : GlobalTheory.FlagPts.CellCont.eval_adjugate_polyMat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:53:24.472264+00:00
-- url     : https://prove2.me/theorems/819fdd3e-7ce5-494c-a917-5524398cd535
-- title:
--   Cell Cont: eval adjugate poly Mat
-- statement:
--   The Cell Cont construction uses the eval adjugate poly Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousCellMap.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousCellMap.lean#L28-L32

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

theorem GlobalTheory.FlagPts.CellCont.eval_adjugate_polyMat (u : AffPts k (CellIdx k V)) (i : ι) (a c : Fin (finrank k (V i))) :
    MvPolynomial.eval u ((polyMat (k := k) (V := V) i).adjugate a c) = (uniMat u i).adjugate a c := by sorry
