-- Prove2me | Theorems.Thm_GlobalTheory_rangeRestrict_comp_subtype_of_orthogonal
-- name    : GlobalTheory.rangeRestrict_comp_subtype_of_orthogonal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:36:18.621294+00:00
-- url     : https://prove2.me/theorems/9fdf265a-9ede-4441-a33e-5a304bdc573d
-- title:
--   Global Theory: range Restrict comp subtype of orthogonal
-- statement:
--   The Global Theory construction uses the range Restrict comp subtype of orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L335-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L335-L342

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

theorem GlobalTheory.rangeRestrict_comp_subtype_of_orthogonal {f : ℕ → Module.End K V}
    (hf : ∀ p q, f p * f q = if p = q then f p else 0) (p : ℕ) :
    (f p).rangeRestrict ∘ₗ (LinearMap.range (f p)).subtype = LinearMap.id := by sorry
