-- Prove2me | Theorems.Thm_GreenTao_linear_forms_convex_mixture
-- name    : GreenTao.linear_forms_convex_mixture
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T21:16:15.250697+00:00
-- url     : https://prove2.me/theorems/d4134021-4ac6-4e18-9b3e-96db8ae5dfd7
-- title:
--   Linear-forms condition is preserved by convex mixing with one
-- statement:
--   Let $\nu_n$ satisfy the $(m_0,t_0,L_0)$ linear-forms condition on the cyclic groups $\mathbb Z/M_n\mathbb Z$. For any fixed $0\le\theta\le1$, define
--
--   $$\mu_n(x)=(1-\theta)\nu_n(x)+\theta.$$
--
--   Then $\mu_n$ satisfies the same $(m_0,t_0,L_0)$ linear-forms condition, including uniformity over all sequences of translation terms. This is the linear-forms part of the smoothing lemma used at the start of the generalized von Neumann argument. It does not assert the separate correlation condition.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §3 Lemma 3.4 and its proof, including the stated extension to (1−θ)ν+θν_const. This theorem isolates the linear-forms assertion; it is not the full pseudorandomness assertion.

import Definitions.Def_GreenTao_Pseudorandom
import Mathlib
open scoped BigOperators Topology
open Filter GreenTao

theorem GreenTao.linear_forms_convex_mixture (M : ℕ → ℕ+) (ν : GreenTao.Family M) (m₀ t₀ L₀ : ℕ)
    (hν : GreenTao.LinearFormsCondition M ν m₀ t₀ L₀)
    (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    GreenTao.LinearFormsCondition M (fun n x => (1 - θ) * ν n x + θ) m₀ t₀ L₀ := by sorry
