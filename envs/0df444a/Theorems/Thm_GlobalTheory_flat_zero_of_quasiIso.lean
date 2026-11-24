-- Prove2me | Theorems.Thm_GlobalTheory_flat_zero_of_quasiIso
-- name    : GlobalTheory.flat_zero_of_quasiIso
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:51:44.414859+00:00
-- url     : https://prove2.me/theorems/e6a47d5c-e6d9-4be2-a5cb-2187ce24f123
-- title:
--   Global Theory: flat zero of quasi Iso
-- statement:
--   The Global Theory construction uses the flat zero of quasi Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L583-L595
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean#L583-L595

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

theorem GlobalTheory.flat_zero_of_quasiIso {K C : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ C)
    [hφ : QuasiIso φ] (hK : ∀ p, 1 ≤ p → Module.Flat R (K.X p))
    (hC : ∀ p, Module.Flat R (C.X p)) (n : ℕ)
    (hnK : ∀ p, n < p → IsZero (K.X p)) (hnC : ∀ p, n < p → IsZero (C.X p)) :
    Module.Flat R (K.X 0) := by sorry
