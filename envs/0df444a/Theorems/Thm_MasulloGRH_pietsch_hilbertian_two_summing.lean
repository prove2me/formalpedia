-- Prove2me | Theorems.Thm_MasulloGRH_pietsch_hilbertian_two_summing
-- name    : MasulloGRH.pietsch_hilbertian_two_summing
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:19:56.793669+00:00
-- url     : https://prove2.me/theorems/81a7ab47-4e85-4c3d-be6c-d78b53b1bc4c
-- title:
--   Pietsch domination: an absolutely summing seminorm pair factors through a 2-summing Hilbertian seminorm
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$ and let $p,q$ be continuous seminorms such that the canonical map $\widetilde E_q\to\widetilde E_p$ is absolutely summing with constant $1$:
--
--   $$\sum_{i=1}^n p(x_i)\le \sup\Big\{\sum_{i=1}^n|f(x_i)| : f\in E',\ |f|\le q\Big\}$$
--
--   for all finite families. Then there is a continuous Hilbertian seminorm $h$ (it satisfies the parallelogram law) with $p\le h\le q$ such that $\widetilde E_q\to\widetilde E_h$ is absolutely $2$-summing with constant $1$:
--
--   $$\sum_{i=1}^n h(x_i)^2\le \sup\Big\{\sum_{i=1}^n|f(x_i)|^2 : f\in E',\ |f|\le q\Big\}.$$
--
--   Proof: by the Pietsch domination theorem there is a Radon probability measure $\mu$ on the weak$^*$-compact set $K=\{f\in E' : |f|\le q\}$ with $p(x)\le\int_K|f(x)|\,d\mu(f)$. Put $h(x)=\big(\int_K|f(x)|^2d\mu(f)\big)^{1/2}$. Then $h$ is a Hilbertian seminorm, $p\le h$ by Cauchy–Schwarz, $h\le q$ since $|f(x)|\le q(x)$ on $K$, and $\sum_i h(x_i)^2=\int_K\sum_i|f(x_i)|^2d\mu\le\sup_K\sum_i|f(x_i)|^2$.
-- source:
--   A. Pietsch, Nuclear Locally Convex Spaces (1972), Thm 2.3.3 (Pietsch domination), §2.3–§3.3 (absolutely 2-summing maps, Hilbert–Schmidt and nuclear composites); A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, §C.2.4.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem pietsch_hilbertian_two_summing (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (p q : Seminorm ℂ E) (hp : Continuous p) (hq : Continuous q)
    (hAS : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ≤ c) →
      ∑ i, p (x i) ≤ c) :
    ∃ h : Seminorm ℂ E, Continuous h ∧ (∀ x, p x ≤ h x) ∧ (∀ x, h x ≤ q x) ∧
      (∀ x y, h (x + y) ^ 2 + h (x - y) ^ 2 = 2 * h x ^ 2 + 2 * h y ^ 2) ∧
      ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
        ∑ i, h (x i) ^ 2 ≤ c := by sorry

end MasulloGRH
