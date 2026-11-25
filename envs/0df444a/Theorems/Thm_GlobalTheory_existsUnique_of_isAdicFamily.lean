-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_of_isAdicFamily
-- name    : GlobalTheory.existsUnique_of_isAdicFamily
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:29:28.737993+00:00
-- url     : https://prove2.me/theorems/e7300033-3bf2-4cae-a1b6-d10c86788384
-- title:
--   Global Theory: exists Unique of is Adic Family
-- statement:
--   The Global Theory construction uses the exists Unique of is Adic Family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L293-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L293-L316

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

theorem GlobalTheory.existsUnique_of_isAdicFamily [IsAdicComplete I R] {X : Scheme.{u}}
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X} (hf : IsAdicFamily I f) :
    ∃! g : Spec (.of R) ⟶ X, ∀ n, adicLevelι I (n + 1) ≫ g = f n := by sorry
