-- Prove2me | Theorems.Thm_GlobalTheory_exists_retraction_tensor_ranges
-- name    : GlobalTheory.exists_retraction_tensor_ranges
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:49:33.639474+00:00
-- url     : https://prove2.me/theorems/28fd48b7-133a-46bf-bdab-054923c9fc83
-- title:
--   Global Theory: exists retraction tensor ranges
-- statement:
--   The Global Theory construction uses the exists retraction tensor ranges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L353-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L353-L381

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
variable {K : Type u} [CommRing K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V']

theorem GlobalTheory.exists_retraction_tensor_ranges {f : ℕ → Module.End K V} {g : ℕ → Module.End K V'}
    (hf : ∀ p q, f p * f q = if p = q then f p else 0)
    (hg : ∀ p q, g p * g q = if p = q then g p else 0) (S : Finset (ℕ × ℕ)) :
    ∃ (I : (∀ x : S, LinearMap.range (f x.1.1) ⊗[K] LinearMap.range (g x.1.2)) →ₗ[K] V ⊗[K] V')
      (Q : V ⊗[K] V' →ₗ[K] ∀ x : S, LinearMap.range (f x.1.1) ⊗[K] LinearMap.range (g x.1.2)),
      (∀ z, I (Q z) = ∑ x ∈ S, TensorProduct.map (f x.1) (g x.2) z) ∧ ∀ w, Q (I w) = w := by sorry
