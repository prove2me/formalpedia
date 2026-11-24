-- Prove2me | Theorems.Thm_GlobalTheory_IsAdicFamily_of_le
-- name    : GlobalTheory.IsAdicFamily.of_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:21:21.953207+00:00
-- url     : https://prove2.me/theorems/f3754e73-3760-4643-9dc1-e34b4aebffec
-- title:
--   Is Adic Family: of le
-- statement:
--   The Is Adic Family construction uses the of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L216-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L216-L221

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

theorem GlobalTheory.IsAdicFamily.of_le {X : Scheme.{u}} {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X}
    (hf : IsAdicFamily I f) {m n : ℕ} (h : m ≤ n) :
    adicLevelMap I (Nat.succ_le_succ h) ≫ f n = f m := by sorry
