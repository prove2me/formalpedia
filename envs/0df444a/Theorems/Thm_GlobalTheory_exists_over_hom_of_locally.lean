-- Prove2me | Theorems.Thm_GlobalTheory_exists_over_hom_of_locally
-- name    : GlobalTheory.exists_over_hom_of_locally
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:43:35.821676+00:00
-- url     : https://prove2.me/theorems/7d430400-1f76-48e3-8c01-7d609f66bb00
-- title:
--   Global Theory: exists over hom of locally
-- statement:
--   The Global Theory construction uses the exists over hom of locally property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MulLeftCompOfPullbackPointEquivMul.lean#L56-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MulLeftCompOfPullbackPointEquivMul.lean#L56-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
open GlobalTheory
variable {R : Type u} [CommRing R]

theorem GlobalTheory.exists_over_hom_of_locally {T Y : Over (Spec (.of R))} [IsReduced T.left]
    [IsSeparated Y.hom]
    (F : ∀ (k : Type u) [Field k] [Algebra R k], (specOver R k ⟶ T) → (specOver R k ⟶ Y))
    (H : ∀ t : T.left, ∃ (U : Over (Spec (.of R))) (j : U ⟶ T) (_ : IsOpenImmersion j.left)
      (f : U ⟶ Y), t ∈ Set.range j.left ∧
        ∀ (k : Type u) [Field k] [Algebra R k] (x : specOver R k ⟶ U), x ≫ f = F k (x ≫ j)) :
    ∃ f : T ⟶ Y, ∀ (k : Type u) [Field k] [Algebra R k] (x : specOver R k ⟶ T),
      x ≫ f = F k x := by sorry
