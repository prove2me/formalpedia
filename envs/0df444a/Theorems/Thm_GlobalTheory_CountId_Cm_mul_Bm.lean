-- Prove2me | Theorems.Thm_GlobalTheory_CountId_Cm_mul_Bm
-- name    : GlobalTheory.CountId.Cm_mul_Bm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:02:47.73223+00:00
-- url     : https://prove2.me/theorems/e1cdeb94-6f22-4a06-8954-cc81e3970fbd
-- title:
--   Count Id: Cm mul Bm
-- statement:
--   The Count Id construction uses the Cm mul Bm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L177-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L177-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {n : ℕ} {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem GlobalTheory.CountId.Cm_mul_Bm {k : Type} [CommRing k] (Y : Gl n k) :
    Cm Y * Bm Y = Matrix.of fun i j : Fin n => mom Y ((i : ℕ) + (j : ℕ)) := by sorry
