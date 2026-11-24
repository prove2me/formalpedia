-- Prove2me | Theorems.Thm_GlobalTheory_OrbCpt_gsum_inter
-- name    : GlobalTheory.OrbCpt.gsum_inter
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:37:49.127318+00:00
-- url     : https://prove2.me/theorems/8b0fea5d-d071-4456-81cf-7985c41956af
-- title:
--   Orb Cpt: gsum inter
-- statement:
--   The Orb Cpt construction uses the gsum inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizer.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizer.lean#L15-L23

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

theorem GlobalTheory.OrbCpt.gsum_inter (X Y : Matrix (Fin r) (Fin r) k) (m : ℕ) :
    X * gsum X Y m - gsum X Y m * Y = X ^ m - Y ^ m := by sorry
