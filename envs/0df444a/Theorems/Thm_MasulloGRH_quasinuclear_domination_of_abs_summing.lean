-- Prove2me | Theorems.Thm_MasulloGRH_quasinuclear_domination_of_abs_summing
-- name    : MasulloGRH.quasinuclear_domination_of_abs_summing
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:10:31.163377+00:00
-- url     : https://prove2.me/theorems/9928ca62-841e-44f3-a78a-57eae24bba63
-- title:
--   Absolutely summing local maps imply quasi-nuclear domination of seminorms
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$ such that for every continuous seminorm $p$ there is a continuous seminorm $q$ with
--
--   $$\sum_{i=1}^n p(x_i)\le \sup\Big\{\sum_{i=1}^n|f(x_i)| : f\in E',\ |f|\le q\Big\}$$
--
--   for all finite families (i.e. every canonical map $\widetilde E_q\to\widetilde E_p$ is absolutely summing). Then every continuous seminorm $p$ is quasi-nuclearly dominated: there are a continuous seminorm $q$, functionals $f_n\in E'$ with $|f_n|\le q$, and $c_n\ge0$ with $\sum c_n<\infty$ such that $p(x)\le\sum_n c_n|f_n(x)|$ for all $x$. Proof: apply the hypothesis twice, $p\le q_1\le q_2$; the composition $\widetilde E_{q_2}\to\widetilde E_{q_1}\to\widetilde E_p$ of two absolutely summing maps is nuclear (Pietsch), $x\mapsto\sum_n c_n f_n(x)y_n$ with $\|f_n\|_{q_2}^*\le1$, $p(y_n)\le1$, whence $p(x)\le\sum_n c_n|f_n(x)|$ with $q=q_2$.
-- source:
--   A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, §C.2.4 (characterization of nuclearity via ℓ¹); A. Pietsch, Nuclear Locally Convex Spaces (1972), Thm 4.2.5 and §3.3 (absolutely summing ⇒ composition nuclear); A. Grothendieck, Produits tensoriels topologiques (1955), Ch. II §3.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem quasinuclear_domination_of_abs_summing (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (hAS : ∀ p : Seminorm ℂ E, Continuous p → ∃ q : Seminorm ℂ E, Continuous q ∧
      ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ≤ c) →
        ∑ i, p (x i) ≤ c) :
    ∀ p : Seminorm ℂ E, Continuous p →
      ∃ (q : Seminorm ℂ E) (f : ℕ → StrongDual ℂ E) (c : ℕ → ℝ),
        Continuous q ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ q x) ∧
        ∀ x, p x ≤ ∑' n, c n * ‖f n x‖ := by sorry

end MasulloGRH
