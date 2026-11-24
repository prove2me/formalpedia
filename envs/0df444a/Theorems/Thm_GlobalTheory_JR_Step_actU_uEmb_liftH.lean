-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_actU_uEmb_liftH
-- name    : GlobalTheory.JR.Step.actU_uEmb_liftH
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:36:36.906555+00:00
-- url     : https://prove2.me/theorems/256866e9-9fc7-44be-a4d6-ab7915cbcb2c
-- title:
--   Step: act U u Emb lift H
-- statement:
--   The Step construction uses the act U u Emb lift H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActHermitianBlockDiagOneLiftLastBasis.lean#L7-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActHermitianBlockDiagOneLiftLastBasis.lean#L7-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActHermitianBlockDiagOneLiftLastBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step

theorem GlobalTheory.JR.Step.actU_uEmb_liftH {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] {r : ℕ} (s : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (ν : E) (l : F) :
    actU (GlobalTheory.JR.Step.uEmb r E s) (GlobalTheory.JR.Step.liftH X ν l) = GlobalTheory.JR.Step.liftH (actU s X) ν l := by sorry
