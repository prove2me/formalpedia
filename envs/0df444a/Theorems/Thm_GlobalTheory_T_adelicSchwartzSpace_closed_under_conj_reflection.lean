-- Prove2me | Theorems.Thm_GlobalTheory_T_adelicSchwartzSpace_closed_under_conj_reflection
-- name    : GlobalTheory.T.adelicSchwartzSpace_closed_under_conj_reflection
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:29.581959+00:00
-- url     : https://prove2.me/theorems/b55e35b7-d529-4f9b-a07f-0401a527a410
-- title:
--   T: adelic Schwartz Space closed under conj reflection
-- statement:
--   The T construction uses the adelic Schwartz Space closed under conj reflection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicSchwartzSpaceClosedUnderConjReflectionStatement.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicSchwartzSpaceClosedUnderConjReflectionStatement.lean#L9-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdelicSchwartzSpaceClosedUnderConjReflection
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdelicSchwartzSpaceClosedUnderConjReflectionStatement
import Theorems.Thm_GlobalTheory_Adopt_adelicSchwartzSpace_closed_under_conj_reflection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.adelicSchwartzSpace_closed_under_conj_reflection : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by sorry
