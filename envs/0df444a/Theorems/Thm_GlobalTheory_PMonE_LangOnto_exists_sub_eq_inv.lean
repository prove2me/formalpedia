-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_LangOnto_exists_sub_eq_inv
-- name    : GlobalTheory.PMonE.LangOnto.exists_sub_eq_inv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:38:41.713776+00:00
-- url     : https://prove2.me/theorems/3a525c8c-0238-434c-ac10-a34b29923774
-- title:
--   Lang Onto: exists sub eq inv
-- statement:
--   The Lang Onto construction uses the exists sub eq inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralSolutionFrobeniusSubMulVecEq.lean#L33-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralSolutionFrobeniusSubMulVecEq.lean#L33-L71

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

theorem GlobalTheory.PMonE.LangOnto.exists_sub_eq_inv {k : Type*} [Field k] [IsAlgClosed k] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {q : ℕ} (hq : 2 ≤ q) (ψ : V →+ V)
    (hψ : ∀ (c : k) (x : V), ψ (c ^ q • x) = c • ψ x) (z : V) : ∃ y, y - ψ y = z := by sorry
