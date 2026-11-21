-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_quasinuclear_domination
-- name    : MasulloGRH.nuclear_quasinuclear_domination
-- status  : Proved
-- author  : @koffie
-- created : 2026-11-20T22:48:54.721921+00:00
-- url     : https://prove2.me/theorems/1398d454-af2f-4292-ba60-6042ca6a58b7
-- title:
--   Nuclear spaces: every continuous seminorm is quasi-nuclearly dominated
-- statement:
--   Let $E$ be a complex vector space with a topology. Call a continuous seminorm $p$ on $E$ **quasi-nuclearly dominated** if there exist a continuous seminorm $q$ on $E$, a sequence $(f_n)_{n\ge0}$ of continuous linear functionals on $E$, and nonnegative reals $(c_n)$ with $\sum_n c_n<\infty$, such that
--
--   $$|f_n(x)|\le q(x)\quad\text{and}\quad p(x)\le\sum_{n=0}^{\infty}c_n\,|f_n(x)|\qquad\text{for all }n\text{ and all }x\in E.$$
--
--   Equivalently, the canonical map $\widetilde E_q\to\widetilde E_p$ between the associated normed spaces is quasi-nuclear in the sense of Pietsch. Here **nuclear** means Grothendieck's condition of Definition C.2.4.1: $E$ is Hausdorff locally convex, and for every Hausdorff locally convex space $F$ the projective topology $\pi$ and the injective topology $\varepsilon$ on $E\otimes F$ coincide.
--
--   **Theorem.** If $E$ is nuclear, then every continuous seminorm on $E$ is quasi-nuclearly dominated.
--
--   This is the forward half of the Grothendieck–Pietsch characterization of nuclear spaces. It converts the tensor-product definition of nuclearity into a seminorm estimate. In that form nuclearity passes directly to subspaces, finite products and similar constructions.
--
--   **Formalization Note** The functionals are elements of `StrongDual ℂ E`; only their values are used. The sum is Lean's `tsum`. It converges because $c_n|f_n(x)|\le c_n\,q(x)$.
-- source:
--   A. Pietsch, *Nuclear Locally Convex Spaces*, Springer (1972), Ch. 4 (quasinuclear mappings and the characterization of nuclear spaces by quasinuclear canonical maps $\widetilde E_q\to\widetilde E_p$) and Ch. 7 (equality of the projective and injective tensor topologies); F. Trèves, *Topological Vector Spaces, Distributions and Kernels* (1967), Ch. 50, Theorem 50.1. Used for Masullo, *The Music of the Primes* (draft 20 Nov 2026), Appendix C, Definition C.2.4.1 (p. 685) and Lemma C.2.4.10 (p. 689). https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem nuclear_quasinuclear_domination (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsNuclear E) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ (q : Seminorm ℂ E) (f : ℕ → StrongDual ℂ E) (c : ℕ → ℝ),
      Continuous q ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖f n x‖ ≤ q x) ∧
      ∀ x, p x ≤ ∑' n, c n * ‖f n x‖ := by sorry

end MasulloGRH
