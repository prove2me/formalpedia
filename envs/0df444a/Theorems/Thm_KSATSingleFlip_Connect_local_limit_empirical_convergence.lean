-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_local_limit_empirical_convergence
-- name    : KSATSingleFlip.Connect.local_limit_empirical_convergence
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:07:10.861251+00:00
-- url     : https://prove2.me/theorems/58e6a08d-b9da-4159-af7a-fdbdb9853472
-- title:
--   Empirical convergence from two-root moment bounds
-- statement:
--   For a sequence of finite weighted spaces with n centered root observables, a uniform diagonal second-moment bound and a uniform off-diagonal cross-moment upper bound tending to zero imply that the total weight of any fixed positive deviation of the empirical average tends to zero. This is the second-moment implication in the empirical conclusion of Lemma 2.4; the model-specific local-limit and cross-moment estimates are separate.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
open Filter
open scoped BigOperators Topology
set_option autoImplicit false

theorem KSATSingleFlip.Connect.local_limit_empirical_convergence (Ω : ℕ → Type) [∀ n, Fintype (Ω n)]
    (p : ∀ n, Ω n → ℝ) (hp : ∀ n ω, 0 ≤ p n ω)
    (X : ∀ n, Fin n → Ω n → ℝ) (C : ℝ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hdiag : ∀ n i, (∑ ω, p n ω * (X n i ω)^2) ≤ C)
    (hoff : ∀ n (i j : Fin n), i ≠ j → (∑ ω, p n ω * X n i ω * X n j ω) ≤ ε n)
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n => ∑ ω, if t ≤ |(∑ i : Fin n, X n i ω)/(n:ℝ)| then p n ω else 0)
      atTop (𝓝 0) := by sorry
