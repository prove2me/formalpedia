-- Prove2me | Theorems.Thm_GlobalTheory_jacFormAlt_apply
-- name    : GlobalTheory.jacFormAlt_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:02:17.328913+00:00
-- url     : https://prove2.me/theorems/7d62b497-15e9-4d54-b2cf-436722c36699
-- title:
--   Global Theory: jac Form Alt apply
-- statement:
--   The Global Theory construction uses the jac Form Alt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L166-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L166-L167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [AddCommGroup N] [Module A N] {D : ℕ}
variable (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)
variable [Module R N] [IsScalarTower R A N] [IsScalarTower R A M]

theorem GlobalTheory.jacFormAlt_apply (f : Fin (D + 1) → A) : jacobianMultilinearTo d ω f = jacForm d ω f := by sorry
