-- Prove2me | Theorems.Thm_GlobalTheory_Desc_exists_smul_mem_of_finiteType_tensor
-- name    : GlobalTheory.Desc.exists_smul_mem_of_finiteType_tensor
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:43:43.408298+00:00
-- url     : https://prove2.me/theorems/d266507f-e932-4201-a185-42ed8aca2270
-- title:
--   Desc: exists smul mem of finite Type tensor
-- statement:
--   The Desc construction uses the exists smul mem of finite Type tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteTypeAwayOfAtPrime.lean#L79-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteTypeAwayOfAtPrime.lean#L79-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteTypeAwayOfAtPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Desc
open scoped TensorProduct

theorem GlobalTheory.Desc.exists_smul_mem_of_finiteType_tensor {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (M : Submonoid R) (h : Algebra.FiniteType (Localization M) (Localization M ⊗[R] C)) :
    ∃ s : Finset C, ∀ c : C, ∃ r ∈ M, algebraMap R C r * c ∈ Algebra.adjoin R (s : Set C) := by sorry
