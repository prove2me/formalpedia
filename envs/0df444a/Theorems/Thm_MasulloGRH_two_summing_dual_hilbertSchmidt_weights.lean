-- Prove2me | Theorems.Thm_MasulloGRH_two_summing_dual_hilbertSchmidt_weights
-- name    : MasulloGRH.two_summing_dual_hilbertSchmidt_weights
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:32:58.081387+00:00
-- url     : https://prove2.me/theorems/655c19f5-93a9-459e-935d-91d59b43d066
-- title:
--   A Bessel system pulled back along a 2-summing Hilbertian map has square-summable dual norms
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$, let $h_2,h_3$ be Hilbertian seminorms on $E$ (parallelogram law) with $h_3$ continuous, and assume the canonical map $\widehat E_{h_3}\to\widehat E_{h_2}$ is $2$-summing with constant $1$: for every finite family $x_1,\dots,x_n\in E$ and $c\in\mathbb R$,
--
--   $$\Big(\forall f\in E',\ |f|\le h_3\ \Rightarrow\ \sum_i |f(x_i)|^2\le c\Big)\ \Longrightarrow\ \sum_i h_2(x_i)^2\le c .$$
--
--   Let $(g_k)_{k\in\mathbb N}\subset E'$ be a Bessel system for $h_2$, i.e. $\sum_k|g_k(x)|^2\le h_2(x)^2$ for all $x\in E$. Then there are $r_k\ge0$ with $\sum_k r_k^2<\infty$ and
--
--   $$|g_k(x)|\le r_k\,h_3(x)\qquad(k\in\mathbb N,\ x\in E).$$
--
--   That is, the $h_3$-dual norms $r_k=\|g_k\|_{h_3}'$ are square-summable. Proof idea: $g_k=\langle\cdot,v_k\rangle_{h_2}$ with $(v_k)$ a Bessel sequence; for the Hilbert–Schmidt map $T:\widehat E_{h_3}\to\widehat E_{h_2}$ and an orthonormal basis $(u_j)$ of $\widehat E_{h_3}$, $\sum_k\|T^*v_k\|^2=\sum_j\sum_k|\langle Tu_j,v_k\rangle|^2\le\sum_j\|Tu_j\|^2\le1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C (nuclear spaces, Hilbertian seminorms); classical: composition of two Hilbert–Schmidt maps is nuclear (Pietsch, Nuclear Locally Convex Spaces, §3.2 and §4.4; Trèves, Topological Vector Spaces, Ch. 48)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem two_summing_dual_hilbertSchmidt_weights (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (h₂ h₃ : Seminorm ℂ E) (hc₃ : Continuous h₃)
    (hpar₂ : ∀ x y, h₂ (x + y) ^ 2 + h₂ (x - y) ^ 2 = 2 * h₂ x ^ 2 + 2 * h₂ y ^ 2)
    (hpar₃ : ∀ x y, h₃ (x + y) ^ 2 + h₃ (x - y) ^ 2 = 2 * h₃ x ^ 2 + 2 * h₃ y ^ 2)
    (h₂₃ : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ h₃ y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
      ∑ i, h₂ (x i) ^ 2 ≤ c)
    (g : ℕ → StrongDual ℂ E)
    (hg : ∀ x, Summable (fun k => ‖g k x‖ ^ 2) ∧ ∑' k, ‖g k x‖ ^ 2 ≤ h₂ x ^ 2) :
    ∃ a : ℕ → ℝ, (∀ k, 0 ≤ a k) ∧ Summable (fun k => a k ^ 2) ∧
      ∀ k x, ‖g k x‖ ≤ a k * h₃ x := by sorry

end MasulloGRH
