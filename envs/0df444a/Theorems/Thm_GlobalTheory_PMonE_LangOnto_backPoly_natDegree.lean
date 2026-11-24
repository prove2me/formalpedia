-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_LangOnto_backPoly_natDegree
-- name    : GlobalTheory.PMonE.LangOnto.backPoly_natDegree
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:39:04.826026+00:00
-- url     : https://prove2.me/theorems/b9da6073-4783-4a89-a95e-2633a30d3486
-- title:
--   Lang Onto: back Poly nat Degree
-- statement:
--   The Lang Onto construction uses the back Poly nat Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralSolutionFrobeniusSubMulVecEq.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralSolutionFrobeniusSubMulVecEq.lean#L19-L31

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

theorem GlobalTheory.PMonE.LangOnto.backPoly_natDegree {k : Type*} [Field k] {q : ℕ} (hq : 2 ≤ q) (n : ℕ) (c : ℕ → k) :
    ∀ j, 1 ≤ (backPoly q n c j).natDegree := by sorry
