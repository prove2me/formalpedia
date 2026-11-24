-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_over_of_isAdicFamily
-- name    : GlobalTheory.existsUnique_over_of_isAdicFamily
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:55.703618+00:00
-- url     : https://prove2.me/theorems/d0b95732-5c43-46c1-8ee9-b26a32fe635c
-- title:
--   Global Theory: exists Unique over of is Adic Family
-- statement:
--   The Global Theory construction uses the exists Unique over of is Adic Family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L318-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L318-L325

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {I}
variable [IsLocalRing R]

theorem GlobalTheory.existsUnique_over_of_isAdicFamily [IsAdicComplete I R] {X S : Scheme.{u}}
    (s : Spec (.of R) ⟶ S) (p : X ⟶ S)
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X} (hf : IsAdicFamily I f)
    (hs : ∀ n, f n ≫ p = adicLevelι I (n + 1) ≫ s) :
    ∃! g : Spec (.of R) ⟶ X, g ≫ p = s ∧ ∀ n, adicLevelι I (n + 1) ≫ g = f n := by sorry
