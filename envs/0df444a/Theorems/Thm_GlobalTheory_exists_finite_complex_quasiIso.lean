-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_complex_quasiIso
-- name    : GlobalTheory.exists_finite_complex_quasiIso
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:18.920806+00:00
-- url     : https://prove2.me/theorems/cbe3cc92-0a14-453f-b976-f5f0bcff0598
-- title:
--   Global Theory: exists finite complex quasi Iso
-- statement:
--   The Global Theory construction uses the exists finite complex quasi Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L521-L581
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L521-L581

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
open Limits
variable {R : Type u} [CommRing R]

theorem GlobalTheory.exists_finite_complex_quasiIso [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (hn : ∀ p, n < p → IsZero (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p)) :
    ∃ (K : CochainComplex (ModuleCat.{u} R) ℕ) (φ : K ⟶ C),
      (∀ p, n < p → IsZero (K.X p)) ∧ (∀ p, Module.Finite R (K.X p)) ∧
      (∀ p, 1 ≤ p → Module.Free R (K.X p)) ∧ QuasiIso φ := by sorry
