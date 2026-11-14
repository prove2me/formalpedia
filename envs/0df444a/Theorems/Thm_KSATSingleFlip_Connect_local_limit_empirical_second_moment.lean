-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_local_limit_empirical_second_moment
-- name    : KSATSingleFlip.Connect.local_limit_empirical_second_moment
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:05:33.060213+00:00
-- url     : https://prove2.me/theorems/dcbd7d79-2154-4af7-99dc-1e2fbe2e9fee
-- title:
--   Second-moment bound for empirical rooted-ball observables
-- statement:
--   For n ≥ 1 real centered observations on a finite weighted probability space, suppose each diagonal second moment is at most C and each off-diagonal cross moment is at most ε ≥ 0. Then the weight of outcomes where the absolute empirical average is at least t > 0 is at most (C/n+ε)/t². This is a finite second-moment ingredient for the empirical conclusion of Lemma 2.4; the joint local-limit and the required moment estimates are separate.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem KSATSingleFlip.Connect.local_limit_empirical_second_moment {Ω : Type} [Fintype Ω] (n : ℕ) (hn : 1 ≤ n)
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Fin n → Ω → ℝ)
    (C ε t : ℝ) (hε : 0 ≤ ε) (ht : 0 < t)
    (hdiag : ∀ i : Fin n, (∑ ω, p ω * (X i ω)^2) ≤ C)
    (hoff : ∀ i j : Fin n, i ≠ j → (∑ ω, p ω * X i ω * X j ω) ≤ ε) :
    (∑ ω, if t ≤ |(∑ i : Fin n, X i ω)/(n:ℝ)| then p ω else 0) ≤
      (C/(n:ℝ)+ε)/t^2 := by sorry
