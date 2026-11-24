-- Prove2me | Theorems.Thm_GlobalTheory_OrbCpt_det_hm_self_ne_zero
-- name    : GlobalTheory.OrbCpt.det_hm_self_ne_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:37:36.47844+00:00
-- url     : https://prove2.me/theorems/19acc77c-0eaa-433d-86df-b7017812c7ae
-- title:
--   Orb Cpt: det hm self ne zero
-- statement:
--   The Orb Cpt construction uses the det hm self ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizer.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizer.lean#L65-L71

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

theorem GlobalTheory.OrbCpt.det_hm_self_ne_zero {p : k[X]} (hp : p.Separable) {X : Matrix (Fin r) (Fin r) k}
    (hX : aeval X p = 0) : (hm p X X).det ≠ 0 := by sorry
