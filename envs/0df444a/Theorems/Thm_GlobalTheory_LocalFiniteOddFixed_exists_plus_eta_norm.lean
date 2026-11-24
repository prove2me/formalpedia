-- Prove2me | Theorems.Thm_GlobalTheory_LocalFiniteOddFixed_exists_plus_eta_norm
-- name    : GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:13:56.5238+00:00
-- url     : https://prove2.me/theorems/faf389e6-ba79-4446-ad0d-a1fd0e6995df
-- title:
--   Local Finite Odd Fixed: exists plus eta norm
-- statement:
--   The Local Finite Odd Fixed construction uses the exists plus eta norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfFinite.lean#L310-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfFinite.lean#L310-L372

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LocalFiniteOddFixed
open GlobalTheory.UnitLemma

theorem GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm (K : UQ) (B : InvAlg K) (f : B.A) (hf : IsIdempotentElem f)
    (hf0 : f ≠ 0) (hfield : ∀ y : B.A, f * y ≠ 0 → ∃ z : B.A, f * y * z = f) (hσ : B.σ f = f) :
    ∃ y : B.A, B.Plus y ∧ y * (1 - f) = 1 - f ∧ K.eta (Algebra.norm K.E y) = -1 := by sorry
