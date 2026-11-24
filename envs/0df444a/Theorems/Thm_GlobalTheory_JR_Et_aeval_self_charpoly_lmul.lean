-- Prove2me | Theorems.Thm_GlobalTheory_JR_Et_aeval_self_charpoly_lmul
-- name    : GlobalTheory.JR.Et.aeval_self_charpoly_lmul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:26:31.655819+00:00
-- url     : https://prove2.me/theorems/a1ad182b-8e43-45b8-8753-6eadc266e38b
-- title:
--   Et: aeval self charpoly lmul
-- statement:
--   The Et construction uses the aeval self charpoly lmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSubringEqOK.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSubringEqOK.lean#L39-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open Polynomial
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JR.Et.aeval_self_charpoly_lmul (A : Et F E) (z : A.K) :
    aeval z (LinearMap.charpoly (Algebra.lmul F A.K z)) = 0 := by sorry
