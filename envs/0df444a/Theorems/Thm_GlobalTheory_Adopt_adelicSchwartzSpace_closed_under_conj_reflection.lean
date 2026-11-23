-- Prove2me | Theorems.Thm_GlobalTheory_Adopt_adelicSchwartzSpace_closed_under_conj_reflection
-- name    : GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:54.593535+00:00
-- url     : https://prove2.me/theorems/98b64170-4056-4d26-aba2-bd9ee66695b8
-- title:
--   Adopt: adelic Schwartz Space closed under conj reflection
-- statement:
--   The Adopt construction uses the adelic Schwartz Space closed under conj reflection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicSchwartzSpaceClosedUnderConjReflection.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicSchwartzSpaceClosedUnderConjReflection.lean#L78-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdelicSchwartzSpaceClosedUnderConjReflection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain

theorem GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by sorry
