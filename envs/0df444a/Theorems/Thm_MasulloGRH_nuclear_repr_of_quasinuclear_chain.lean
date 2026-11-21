-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_repr_of_quasinuclear_chain
-- name    : MasulloGRH.nuclear_repr_of_quasinuclear_chain
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:19:40.276287+00:00
-- url     : https://prove2.me/theorems/a97707be-23bb-4aaa-8979-7b12448355dd
-- title:
--   Product of two quasi-nuclear canonical maps is nuclear, with representing points in $E$
-- statement:
--   Let $E$ be a complex vector space and let $q,p,r$ be seminorms on $E$. Assume the two canonical maps $E_r\to E_p\to E_q$ are **quasi-nuclear** in Pietsch's sense, witnessed explicitly: there are linear functionals $g_n,h_n$ on $E$ and nonnegative summable sequences $(\mu_n),(\nu_n)$ with
--
--   $$|g_n(x)|\le p(x),\qquad q(x)\le\sum_n \mu_n|g_n(x)|,\qquad |h_n(x)|\le r(x),\qquad p(x)\le \sum_n \nu_n |h_n(x)|\qquad(x\in E).$$
--
--   Then the composite canonical map $E_r\to E_q$ is **nuclear**, with the representing vectors taken in $E$ itself: there exist linear functionals $k_n$ on $E$ with $|k_n(x)|\le r(x)$, points $y_n\in E$ with $q(y_n)\le 1$, and nonnegative summable $(c_n)$ such that for every $x\in E$
--
--   $$q\Big(x-\sum_{n<N} c_n\,k_n(x)\,y_n\Big)\longrightarrow 0\qquad (N\to\infty).$$
--
--   This is the classical fact that the product of two quasi-nuclear maps is nuclear (Pietsch, Nuclear Locally Convex Spaces, §3.3), applied to the canonical maps $\widehat E_r\to\widehat E_p\to\widehat E_q$; the representing vectors $\hat y_n\in\widehat E_q$ are then replaced by points of $E$ by expanding each $\hat y_n$ as a rapidly convergent series of elements of $E$ (dense in $\widehat E_q$) and re-indexing, which keeps $\sum c_n<\infty$ and preserves convergence since the double series is absolutely convergent in $\widehat E_q$.
--
--   **Formalization note.** The sums $\sum_n\mu_n|g_n(x)|$ are Lean `tsum`s; they converge since $\mu_n|g_n(x)|\le\mu_n p(x)$. No topology on $E$ is needed.
-- source:
--   A. Pietsch, Nuclear Locally Convex Spaces, Springer (1972), §3.2–3.3 (quasinuclear and nuclear maps; the product of two quasinuclear maps is nuclear); H. H. Schaefer, Topological Vector Spaces (GTM 3), Ch. III §7. Used for Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, Lemma C.2.4.10 item 2 (p. 689).

import Mathlib

set_option autoImplicit false

namespace MasulloGRH

open Filter Topology

universe u

theorem nuclear_repr_of_quasinuclear_chain (E : Type u) [AddCommGroup E] [Module ℂ E]
    (q p r : Seminorm ℂ E)
    (g : ℕ → E →ₗ[ℂ] ℂ) (μ : ℕ → ℝ) (hμ0 : ∀ n, 0 ≤ μ n) (hμ : Summable μ)
    (hg : ∀ n x, ‖g n x‖ ≤ p x) (hq : ∀ x, q x ≤ ∑' n, μ n * ‖g n x‖)
    (h : ℕ → E →ₗ[ℂ] ℂ) (ν : ℕ → ℝ) (hν0 : ∀ n, 0 ≤ ν n) (hν : Summable ν)
    (hh : ∀ n x, ‖h n x‖ ≤ r x) (hp : ∀ x, p x ≤ ∑' n, ν n * ‖h n x‖) :
    ∃ (k : ℕ → E →ₗ[ℂ] ℂ) (y : ℕ → E) (c : ℕ → ℝ),
      (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖k n x‖ ≤ r x) ∧ (∀ n, q (y n) ≤ 1) ∧
      ∀ x, Tendsto (fun N => q (x - ∑ n ∈ Finset.range N, (c n * k n x) • y n)) atTop (𝓝 0) := by sorry

end MasulloGRH
