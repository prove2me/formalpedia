-- Prove2me | Theorems.Thm_GlobalTheory_Per_single_mem_of_support_subset
-- name    : GlobalTheory.Per.single_mem_of_support_subset
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:50:26.958155+00:00
-- url     : https://prove2.me/theorems/e9f0a633-6827-4681-8559-88560a060fa9
-- title:
--   Per: single mem of support subset
-- statement:
--   The Per construction uses the single mem of support subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SingleMemOfSupportSubset.lean#L8-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SingleMemOfSupportSubset.lean#L8-L60

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SingleMemOfSupportSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.Per

theorem GlobalTheory.Per.single_mem_of_support_subset {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D]
    (u : LL) (Λ : Submodule LL (ℤ → D)) (hu : u ≠ 0) (hr : ∀ k : ℤ, k ≠ 0 → u ^ k ≠ 1)
    (hγ : ∀ x ∈ Λ, (fun k => u ^ k • x k) ∈ Λ) (S : Finset ℤ) :
    ∀ x ∈ Λ, (∀ k, k ∉ S → x k = 0) → ∀ k, Pi.single k (x k) ∈ Λ := by sorry
