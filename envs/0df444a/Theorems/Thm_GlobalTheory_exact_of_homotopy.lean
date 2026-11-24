-- Prove2me | Theorems.Thm_GlobalTheory_exact_of_homotopy
-- name    : GlobalTheory.exact_of_homotopy
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:19:56.396796+00:00
-- url     : https://prove2.me/theorems/3b02c872-19d7-4848-bfe2-eba4b6f4eea5
-- title:
--   Global Theory: exact of homotopy
-- statement:
--   The Global Theory construction uses the exact of homotopy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L137-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L137-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Function
open GlobalTheory
variable {R : Type*} [CommRing R] {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

theorem GlobalTheory.exact_of_homotopy {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    {s : B →ₗ[R] A} {t : C →ₗ[R] B} (h : f ∘ₗ s + t ∘ₗ g = LinearMap.id) : Exact f g := by sorry
