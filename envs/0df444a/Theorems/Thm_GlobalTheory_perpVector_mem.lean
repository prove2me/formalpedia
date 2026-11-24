-- Prove2me | Theorems.Thm_GlobalTheory_perpVector_mem
-- name    : GlobalTheory.perpVector_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:23.596388+00:00
-- url     : https://prove2.me/theorems/8853bd55-e2ed-4942-a84d-3a6f7868d115
-- title:
--   Global Theory: perp Vector mem
-- statement:
--   The Global Theory construction uses the perp Vector mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L61-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
variable {A : Type*} [CommRing A] [Algebra A R]

theorem GlobalTheory.perpVector_mem [Module A M] [IsScalarTower A R M] (L : Submodule A M)
    (ε : ι → Module.Dual R M) {e' : ι → M} {g : M} (he' : ∀ a, e' a ∈ L) (hgL : g ∈ L)
    (he : ∀ a a', ε a (e' a') ∈ (algebraMap A R).range)
    (hg : ∀ a, ε a g ∈ (algebraMap A R).range) : perpVector ε e' g ∈ L := by sorry
