-- Prove2me | Theorems.Thm_GlobalTheory_altRestrictScalars_apply
-- name    : GlobalTheory.altRestrictScalars_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:40.99441+00:00
-- url     : https://prove2.me/theorems/04f670b2-6863-46a8-b44a-ca0d076a59f4
-- title:
--   Global Theory: alt Restrict Scalars apply
-- statement:
--   The Global Theory construction uses the alt Restrict Scalars apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L181-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AlternatingMapSumSmulEqDetSmul.lean#L181-L182

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
variable (A : Type*) {B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] {D : ℕ}

theorem GlobalTheory.altRestrictScalars_apply (ω : M [⋀^Fin D]→ₗ[B] N) (v : Fin D → M) :
    altRestrictScalars A ω v = ω v := by sorry

attribute [defeq] GlobalTheory.altRestrictScalars_apply
