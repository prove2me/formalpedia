-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_LangOnto_backPoly_succ
-- name    : GlobalTheory.PMonE.LangOnto.backPoly_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:45.204908+00:00
-- url     : https://prove2.me/theorems/6a8ff9ba-0c5d-4584-b3de-81650799583b
-- title:
--   Lang Onto: back Poly succ
-- statement:
--   The Lang Onto construction uses the back Poly succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralSolutionFrobeniusSubMulVecEq.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralSolutionFrobeniusSubMulVecEq.lean#L16-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralSolutionFrobeniusSubMulVecEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LangOnto
open Polynomial Finset GlobalTheory.PMonE

theorem GlobalTheory.PMonE.LangOnto.backPoly_succ {k : Type*} [Field k] (q n : ℕ) (c : ℕ → k) (j : ℕ) :
    backPoly q n c (j + 1) = backPoly q n c j ^ q - C (c (n - j)) * X := by sorry
