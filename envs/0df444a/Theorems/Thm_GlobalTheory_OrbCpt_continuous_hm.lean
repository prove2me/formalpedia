-- Prove2me | Theorems.Thm_GlobalTheory_OrbCpt_continuous_hm
-- name    : GlobalTheory.OrbCpt.continuous_hm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:38:19.120344+00:00
-- url     : https://prove2.me/theorems/3d1cf19c-f7c8-4ebf-9a31-6e097e5d5c0a
-- title:
--   Orb Cpt: continuous hm
-- statement:
--   The Orb Cpt construction uses the continuous hm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizer.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizer.lean#L59-L63

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

theorem GlobalTheory.OrbCpt.continuous_hm (p : k[X]) :
    Continuous fun q : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin r) k => hm p q.1 q.2 := by sorry
