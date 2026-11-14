-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_exploration_collision_bound
-- name    : KSATSingleFlip.Connect.exploration_collision_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:08:35.158223+00:00
-- url     : https://prove2.me/theorems/8cece441-1bd2-478b-84eb-47e43ad54f9c
-- title:
--   Finite exploration collision union bound
-- statement:
--   For m labels on a finite nonnegative weighted probability space, if every pair of distinct sampled labels collides with weight at most 1/n, then the total weight of an outcome with any collision is at most m²/n. This is a generic union-bound ingredient in the breadth-first exploration underlying Lemma 2.4; establishing the pairwise hypotheses for the three formula laws remains separate.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem KSATSingleFlip.Connect.exploration_collision_bound {Ω : Type} [Fintype Ω] (m n : ℕ) (hn : 0 < n)
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Fin m → Ω → Fin n)
    (hpair : ∀ i j : Fin m, i ≠ j → (∑ ω, if X i ω = X j ω then p ω else 0) ≤ 1/(n:ℝ)) :
    (∑ ω, if ∃ i j : Fin m, i ≠ j ∧ X i ω = X j ω then p ω else 0) ≤
      (m:ℝ)^2/(n:ℝ) := by sorry
