-- Prove2me | Theorems.Thm_GlobalTheory_compositum_finite_formallyUnramified
-- name    : GlobalTheory.compositum_finite_formallyUnramified
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:31.344068+00:00
-- url     : https://prove2.me/theorems/39bde1aa-a730-446f-a962-7c7ff6de5127
-- title:
--   Global Theory: compositum finite formally Unramified
-- statement:
--   The Global Theory construction uses the compositum finite formally Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCommonUnramifiedExtension.lean#L7-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCommonUnramifiedExtension.lean#L7-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCommonUnramifiedExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.compositum_finite_formallyUnramified : ∀ {k K L : Type} [Field k] [Field K] [Field L] (i : k →+* K) (j : k →+* L), i.Finite → i.FormallyUnramified → ∃ (M : Type) (_ : Field M) (u : K →+* M) (v : L →+* M), u.comp i = v.comp j ∧ v.Finite ∧ v.FormallyUnramified := by sorry
