-- Prove2me | Theorems.Thm_MasulloGRH_hilbertian_two_summing_bessel_expansion
-- name    : MasulloGRH.hilbertian_two_summing_bessel_expansion
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:32:58.051848+00:00
-- url     : https://prove2.me/theorems/4599fca6-8bdc-43f0-ae49-b2740b9ddddf
-- title:
--   A 2-summing map between Hilbertian seminorms admits an $\ell^2$-weighted Bessel expansion
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$, let $h_1,h_2,h_3$ be seminorms on $E$ with $h_3$ continuous and $h_2\le h_3$, and suppose $h_1,h_2$ are **Hilbertian** (they satisfy the parallelogram law). Assume the canonical map $\widehat E_{h_2}\to\widehat E_{h_1}$ is $2$-summing with constant $1$: for every finite family $x_1,\dots,x_n\in E$ and $c\in\mathbb R$,
--
--   $$\Big(\forall f\in E',\ |f|\le h_2\ \Rightarrow\ \sum_i |f(x_i)|^2\le c\Big)\ \Longrightarrow\ \sum_i h_1(x_i)^2\le c .$$
--
--   Then there are continuous linear functionals $g_k\in E'$ and numbers $b_k\ge 0$ with $\sum_k b_k^2<\infty$ such that $(g_k)$ is a **Bessel system** for $h_2$,
--
--   $$\sum_k |g_k(x)|^2\le h_2(x)^2\qquad(x\in E),$$
--
--   and
--
--   $$h_1(x)\le \sum_k b_k\,|g_k(x)|\qquad(x\in E).$$
--
--   Proof idea: the canonical map $S:\widehat E_{h_2}\to\widehat E_{h_1}$ is Hilbert–Schmidt; for an orthonormal basis $(e_i)$ of $\widehat E_{h_2}$ only countably many $Se_i$ are nonzero, and one takes $g_k=\langle\cdot,e_k\rangle_{h_2}$, $b_k=h_1(Se_k)$, using $Sx=\sum_k\langle x,e_k\rangle Se_k$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C (nuclear spaces, Hilbertian seminorms); classical: composition of two Hilbert–Schmidt maps is nuclear (Pietsch, Nuclear Locally Convex Spaces, §3.2 and §4.4; Trèves, Topological Vector Spaces, Ch. 48)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem hilbertian_two_summing_bessel_expansion (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (h₁ h₂ h₃ : Seminorm ℂ E) (hc₃ : Continuous h₃) (h₂₃ : ∀ x, h₂ x ≤ h₃ x)
    (hpar₁ : ∀ x y, h₁ (x + y) ^ 2 + h₁ (x - y) ^ 2 = 2 * h₁ x ^ 2 + 2 * h₁ y ^ 2)
    (hpar₂ : ∀ x y, h₂ (x + y) ^ 2 + h₂ (x - y) ^ 2 = 2 * h₂ x ^ 2 + 2 * h₂ y ^ 2)
    (h₁₂ : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ h₂ y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
      ∑ i, h₁ (x i) ^ 2 ≤ c) :
    ∃ (g : ℕ → StrongDual ℂ E) (b : ℕ → ℝ), (∀ k, 0 ≤ b k) ∧ Summable (fun k => b k ^ 2) ∧
      (∀ x, Summable (fun k => ‖g k x‖ ^ 2) ∧ ∑' k, ‖g k x‖ ^ 2 ≤ h₂ x ^ 2) ∧
      ∀ x, h₁ x ≤ ∑' k, b k * ‖g k x‖ := by sorry

end MasulloGRH
