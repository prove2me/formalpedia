-- Prove2me | Theorems.Thm_GlobalTheory_finiteType_invariants_and_finite
-- name    : GlobalTheory.finiteType_invariants_and_finite
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:15.435863+00:00
-- url     : https://prove2.me/theorems/d8ed7280-907e-4384-8aa0-b44116008b3a
-- title:
--   Global Theory: finite Type invariants and finite
-- statement:
--   The Global Theory construction uses the finite Type invariants and finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteTypeInvariantsFiniteGroupAndFinite.lean#L5-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteTypeInvariantsFiniteGroupAndFinite.lean#L5-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteTypeInvariantsFiniteGroupAndFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.finiteType_invariants_and_finite (R : Type) [CommRing R] [IsNoetherianRing R]
    (C' : Type) [CommRing C'] [Algebra R C'] [Algebra.FiniteType R C']
    (G : Type) [Group G] [Finite G] (act : G →* (C' ≃ₐ[R] C')) (C : Subalgebra R C')
    (hC : ∀ x, x ∈ C ↔ ∀ σ, act σ x = x) :
    Algebra.FiniteType R C ∧ Module.Finite C C' := by sorry
