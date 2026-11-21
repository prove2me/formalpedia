-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_of_quasinuclear_domination
-- name    : MasulloGRH.nuclear_of_quasinuclear_domination
-- status  : Proved
-- author  : @koffie
-- created : 2026-11-20T22:48:57.04817+00:00
-- url     : https://prove2.me/theorems/aa3355e2-a2f3-4811-bd78-63c8f3277f38
-- title:
--   Nuclear spaces: quasi-nuclear domination of all seminorms implies nuclearity
-- statement:
--   Let $E$ be a complex vector space with a topology. Call a continuous seminorm $p$ on $E$ **quasi-nuclearly dominated** if there exist a continuous seminorm $q$ on $E$, a sequence $(f_n)_{n\ge0}$ of continuous linear functionals on $E$, and nonnegative reals $(c_n)$ with $\sum_n c_n<\infty$, such that
--
--   $$|f_n(x)|\le q(x)\quad\text{and}\quad p(x)\le\sum_{n=0}^{\infty}c_n\,|f_n(x)|\qquad\text{for all }n\text{ and all }x\in E.$$
--
--   Equivalently, the canonical map $\widetilde E_q\to\widetilde E_p$ between the associated normed spaces is quasi-nuclear in the sense of Pietsch. Here **nuclear** means Grothendieck's condition of Definition C.2.4.1: $E$ is Hausdorff locally convex, and for every Hausdorff locally convex space $F$ the projective topology $\pi$ and the injective topology $\varepsilon$ on $E\otimes F$ coincide.
--
--   **Theorem.** Let $E$ be a Hausdorff locally convex space in which every continuous seminorm is quasi-nuclearly dominated. Then $E$ is nuclear.
--
--   This is the converse half of the Grothendieck–Pietsch characterization. Iterating the domination twice makes the canonical maps $\widetilde E_{q'}\to\widetilde E_p$ nuclear, since a product of two quasi-nuclear maps is nuclear. Nuclear canonical maps make every $\pi$-continuous seminorm on $E\otimes F$ continuous for $\varepsilon$. Together with the forward half, this reduces the permanence properties of Lemma C.2.4.10 to seminorm estimates.
--
--   **Formalization Note** The Hausdorff locally convex hypothesis is the predicate `IsHLCS` of the mission's definition file. The functionals are elements of `StrongDual ℂ E`, and the sum is Lean's `tsum`.
-- source:
--   A. Pietsch, *Nuclear Locally Convex Spaces*, Springer (1972), Ch. 4 (quasinuclear mappings and the characterization of nuclear spaces by quasinuclear canonical maps $\widetilde E_q\to\widetilde E_p$) and Ch. 7 (equality of the projective and injective tensor topologies); F. Trèves, *Topological Vector Spaces, Distributions and Kernels* (1967), Ch. 50, Theorem 50.1. Used for Masullo, *The Music of the Primes* (draft 20 Nov 2026), Appendix C, Definition C.2.4.1 (p. 685) and Lemma C.2.4.10 (p. 689). https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem nuclear_of_quasinuclear_domination (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E)
    (hdom : ∀ p : Seminorm ℂ E, Continuous p →
      ∃ (q : Seminorm ℂ E) (f : ℕ → StrongDual ℂ E) (c : ℕ → ℝ),
        Continuous q ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ q x) ∧
        ∀ x, p x ≤ ∑' n, c n * ‖f n x‖) :
    IsNuclear E := by sorry

end MasulloGRH
