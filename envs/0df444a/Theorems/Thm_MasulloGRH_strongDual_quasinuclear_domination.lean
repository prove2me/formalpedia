-- Prove2me | Theorems.Thm_MasulloGRH_strongDual_quasinuclear_domination
-- name    : MasulloGRH.strongDual_quasinuclear_domination
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:00:07.270474+00:00
-- url     : https://prove2.me/theorems/84acf2f4-6346-4e83-9927-2031d6d9db28
-- title:
--   Continuous seminorms on the strong dual of a nuclear Fréchet space are quasi-nuclearly dominated
-- statement:
--   Let $E$ be a nuclear Fréchet space over $\mathbb C$ and let $E'_\beta$ be its strong dual (continuous linear functionals on $E$ with the topology of uniform convergence on bounded subsets of $E$). Then every continuous seminorm on $E'_\beta$ is **quasi-nuclearly dominated**: for every continuous seminorm $p$ on $E'_\beta$ there exist a continuous seminorm $q$ on $E'_\beta$, continuous linear functionals $\varphi_n$ on $E'_\beta$ ($n\ge0$) and reals $c_n\ge0$ with $\sum_n c_n<\infty$, such that
--
--   $$|\varphi_n(f)|\le q(f)\quad\text{and}\quad p(f)\le\sum_{n=0}^{\infty}c_n\,|\varphi_n(f)|\qquad\text{for all } n \text{ and all } f\in E'.$$
--
--   Here a Fréchet space is a complete metrizable locally convex space, and **nuclear** is Grothendieck's condition of Definition C.2.4.1 of the source: for every Hausdorff locally convex $F$ the projective and injective topologies on $E\otimes F$ coincide.
--
--   Combined with the Grothendieck–Pietsch characterization (a Hausdorff locally convex space all of whose continuous seminorms are quasi-nuclearly dominated is nuclear), this yields nuclearity of the strong dual of a nuclear Fréchet space.
--
--   **Formalization Note** The strong dual is Mathlib's `StrongDual ℂ E` and the functionals $\varphi_n$ are elements of `StrongDual ℂ (StrongDual ℂ E)`. The domination is stated exactly in the form of the hypothesis of `MasulloGRH.nuclear_of_quasinuclear_domination`; the sum is Lean's `tsum`.
-- source:
--   H. H. Schaefer, Topological Vector Spaces (2nd ed.), IV.9.6 and III.7.2–7.3 (nuclear spaces, bounded sets of nuclear Fréchet spaces); A. Pietsch, Nuclear Locally Convex Spaces (1972), Ch. 4; A. M. Masullo, The Music of the Primes (draft 2026), Appendix C, Lemma C.2.4.11 (forward direction).

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strongDual_quasinuclear_domination (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E)
    (p : Seminorm ℂ (StrongDual ℂ E)) (hp : Continuous p) :
    ∃ (q : Seminorm ℂ (StrongDual ℂ E)) (f : ℕ → StrongDual ℂ (StrongDual ℂ E)) (c : ℕ → ℝ),
      Continuous q ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ q x) ∧
      ∀ x, p x ≤ ∑' n, c n * ‖f n x‖ := by sorry

end MasulloGRH
