-- Prove2me | Theorems.Thm_GlobalTheory_OrbCpt_hm_inter
-- name    : GlobalTheory.OrbCpt.hm_inter
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:37:47.678477+00:00
-- url     : https://prove2.me/theorems/2bd0a1d7-0d3d-48a5-b068-5144f5136a42
-- title:
--   Orb Cpt: hm inter
-- statement:
--   The Orb Cpt construction uses the hm inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizer.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizer.lean#L41-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology Polynomial
noncomputable section
open GlobalTheory GlobalTheory.OrbCpt
variable {k : Type} [NontriviallyNormedField k] {r : ℕ}

theorem GlobalTheory.OrbCpt.hm_inter (p : k[X]) (X Y : Matrix (Fin r) (Fin r) k) :
    X * hm p X Y - hm p X Y * Y = aeval X p - aeval Y p := by sorry
