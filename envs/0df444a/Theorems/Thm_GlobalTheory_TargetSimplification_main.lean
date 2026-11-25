-- Prove2me | Theorems.Thm_GlobalTheory_TargetSimplification_main
-- name    : GlobalTheory.TargetSimplification.main
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:40:41.363558+00:00
-- url     : https://prove2.me/theorems/99ab751e-e41d-4511-84b2-7da5633c934a
-- title:
--   Target Simplification: main
-- statement:
--   The Target Simplification construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsMoreBis.lean#L5-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsMoreBis.lean#L5-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsMoreBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TargetSimplification

theorem GlobalTheory.TargetSimplification.main {E V : Type} [Field E] [CharZero E] [AddCommGroup V] [Module E V] {s : E →+* E} {r : ℕ}
  (B : V →ₛₗ[s] V →ₗ[E] E) (hB : ∀ u v : V, B u v = s (B v u))
  {x y : Fin r → V} (hx : ∀ i j, B (x i) (x j) = 0) (hy : ∀ i j, B (y i) (y j) = 0)
  (hxy : ∀ i j, B (x i) (y j) = if i = j then 1 else 0)
  {z w₀ : V} (hxz : ∀ i, B (x i) z = 0) (hyz : ∀ i, B (y i) z = 0) (hzz : B z z = 0)
  (hzw : B z w₀ = 1) :
  ∃ (x' y' : Fin (r+1) → V), (∀ i j, B (x' i) (x' j) = 0) ∧ (∀ i j, B (y' i) (y' j) = 0) ∧
    (∀ i j, B (x' i) (y' j) = if i = j then 1 else 0) ∧ ∀ i : Fin r, x' (Fin.castSucc i) = x i := by sorry
