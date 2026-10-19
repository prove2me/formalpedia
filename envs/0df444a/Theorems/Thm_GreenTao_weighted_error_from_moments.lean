-- Prove2me | Theorems.Thm_GreenTao_weighted_error_from_moments
-- name    : GreenTao.weighted_error_from_moments
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T21:16:15.461994+00:00
-- url     : https://prove2.me/theorems/7c1874c2-8625-4bc7-bad0-be20e03097f4
-- title:
--   Three weighted moments control all dominated errors uniformly
-- statement:
--   For each $n$, let $A_n$ be a finite set and let $V_n,W_n:A_n\to\mathbb R$, with $V_n\ge0$. Suppose
--
--   $$\mathbb E V_n\longrightarrow1,\qquad\mathbb E(W_nV_n)\longrightarrow1,\qquad\mathbb E(W_n^2V_n)\longrightarrow1.$$
--
--   Then for every $\eta>0$, all sufficiently large $n$ satisfy, uniformly over real test functions $H$ on $A_n$,
--
--   $$|H|\le V_n\quad\Longrightarrow\quad\left|\mathbb E((W_n-1)H)\right|\le\eta.$$
--
--   The finite sets may vary with $n$. No sign restriction is imposed on $W_n$ or $H$. This is the uniform dominated-error consequence of the three moments used to show that a pseudorandom measure covers its cubes uniformly.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §5, the Cauchy–Schwarz reduction immediately before Lemma 5.5 and the expansion into q=0,1,2 moments in its proof. This auxiliary general finite-space formulation isolates that analytic implication.

import Definitions.Def_GreenTao_Pseudorandom
import Mathlib
open scoped BigOperators Topology
open Filter GreenTao

theorem GreenTao.weighted_error_from_moments (A : ℕ → Type) [∀ n, Fintype (A n)]
    (V W : ∀ n, A n → ℝ) (hV : ∀ n x, 0 ≤ V n x)
    (h₀ : Tendsto (fun n => avg (V n)) atTop (𝓝 1))
    (h₁ : Tendsto (fun n => avg (fun x => W n x * V n x)) atTop (𝓝 1))
    (h₂ : Tendsto (fun n => avg (fun x => W n x ^ 2 * V n x)) atTop (𝓝 1)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      ∀ H : A n → ℝ, (∀ x, |H x| ≤ V n x) →
        |avg (fun x => (W n x - 1) * H x)| ≤ η := by sorry
