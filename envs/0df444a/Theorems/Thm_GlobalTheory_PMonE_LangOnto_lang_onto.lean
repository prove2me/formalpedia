-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_LangOnto_lang_onto
-- name    : GlobalTheory.PMonE.LangOnto.lang_onto
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:38:49.243898+00:00
-- url     : https://prove2.me/theorems/3129b999-47c7-46d4-b367-dba12d2e19b4
-- title:
--   Lang Onto: lang onto
-- statement:
--   The Lang Onto construction uses the lang onto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralSolutionFrobeniusSubMulVecEq.lean#L102-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralSolutionFrobeniusSubMulVecEq.lean#L102-L127

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

theorem GlobalTheory.PMonE.LangOnto.lang_onto : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ)
    [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F,
    (∀ i j, ‖A i j‖ ≤ 1) → ∀ b : m → F, Integral b →
      ∃ x : m → F, Integral x ∧ ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by sorry
