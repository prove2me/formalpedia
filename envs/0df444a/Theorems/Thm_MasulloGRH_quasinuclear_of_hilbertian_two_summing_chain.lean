-- Prove2me | Theorems.Thm_MasulloGRH_quasinuclear_of_hilbertian_two_summing_chain
-- name    : MasulloGRH.quasinuclear_of_hilbertian_two_summing_chain
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:20:08.314711+00:00
-- url     : https://prove2.me/theorems/a641b57b-62a7-4d68-8490-e64b7063b06d
-- title:
--   A chain of two 2-summing maps between Hilbertian seminorms is quasi-nuclear
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$ and let $h_1,h_2,h_3$ be Hilbertian seminorms (each satisfies the parallelogram law), $h_3$ continuous, such that $\widetilde E_{h_2}\to\widetilde E_{h_1}$ and $\widetilde E_{h_3}\to\widetilde E_{h_2}$ are absolutely $2$-summing with constant $1$, i.e. for all finite families
--
--   $$\sum_i h_j(x_i)^2\le\sup\Big\{\sum_i|f(x_i)|^2 : f\in E',\ |f|\le h_{j+1}\Big\}\qquad(j=1,2).$$
--
--   Then there are $f_n\in E'$ with $|f_n|\le h_3$ and $c_n\ge 0$ with $\sum_n c_n<\infty$ such that $h_1(x)\le\sum_n c_n|f_n(x)|$ for all $x\in E$.
--
--   Proof: taking $n=1$ gives $h_1\le h_2\le h_3$, so the identity of $E$ extends to maps $T:H_3\to H_2$ and $S:H_2\to H_1$ between the Hilbert completions. An absolutely $2$-summing operator between Hilbert spaces is Hilbert–Schmidt (test the inequality on finite orthonormal families, by Bessel), so $ST$ is trace class: $ST=\sum_k\sigma_k\langle\cdot,u_k\rangle v_k$ with $(u_k)$, $(v_k)$ orthonormal and $\sum_k\sigma_k<\infty$. Hence $h_1(x)=\|STx\|\le\sum_k\sigma_k|\langle x,u_k\rangle_{H_3}|$, and $f_k=\langle\cdot,u_k\rangle_{H_3}$ satisfies $|f_k|\le h_3$ (so it is continuous).
-- source:
--   A. Pietsch, Nuclear Locally Convex Spaces (1972), Thm 2.3.3 (Pietsch domination), §2.3–§3.3 (absolutely 2-summing maps, Hilbert–Schmidt and nuclear composites); A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, §C.2.4.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem quasinuclear_of_hilbertian_two_summing_chain (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (h₁ h₂ h₃ : Seminorm ℂ E) (hc₃ : Continuous h₃)
    (hpar₁ : ∀ x y, h₁ (x + y) ^ 2 + h₁ (x - y) ^ 2 = 2 * h₁ x ^ 2 + 2 * h₁ y ^ 2)
    (hpar₂ : ∀ x y, h₂ (x + y) ^ 2 + h₂ (x - y) ^ 2 = 2 * h₂ x ^ 2 + 2 * h₂ y ^ 2)
    (hpar₃ : ∀ x y, h₃ (x + y) ^ 2 + h₃ (x - y) ^ 2 = 2 * h₃ x ^ 2 + 2 * h₃ y ^ 2)
    (h₁₂ : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ h₂ y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
      ∑ i, h₁ (x i) ^ 2 ≤ c)
    (h₂₃ : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ h₃ y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
      ∑ i, h₂ (x i) ^ 2 ≤ c) :
    ∃ (f : ℕ → StrongDual ℂ E) (c : ℕ → ℝ),
      (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ h₃ x) ∧
      ∀ x, h₁ x ≤ ∑' n, c n * ‖f n x‖ := by sorry

end MasulloGRH
