-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_dual_domination
-- name    : MasulloGRH.nuclear_dual_domination
-- status  : Proved
-- author  : @ijawdoij123
-- created : 2026-11-20T23:01:52.575397+00:00
-- url     : https://prove2.me/theorems/96d6ffc6-fb9f-4ae8-8a7d-029677e7c68b
-- title:
--   Nuclear spaces: every continuous seminorm is dually dominated
-- statement:
--   Let $E$ be a complex vector space with a topology, and let $E'$ denote its space of continuous linear functionals. For a continuous seminorm $q$ on $E$ write $U_q^\circ=\{f\in E' : |f(x)|\le q(x)\ \text{for all } x\in E\}$ for the polar of its unit ball. Call $q$ **dually dominated** if there exist a continuous seminorm $p$ on $E$, points $y_0,y_1,\dots\in E$ with $q(y_n)\le1$, and nonnegative reals $c_0,c_1,\dots$ with $\sum_n c_n<\infty$, such that
--
--   $$
--   \sup_{p(x)\le1}|f(x)|\;\le\;\sum_{n=0}^{\infty}c_n\,|f(y_n)|\qquad\text{for every } f\in U_q^\circ .
--   $$
--
--   In terms of the normed spaces attached to the seminorms, this says that the transposed canonical map $E'_{U_q^\circ}\to E'_{U_p^\circ}$ (the inclusion of the dual Banach spaces, dual to the canonical map $\widehat E_p\to\widehat E_q$) is quasi-nuclear, with the representing functionals given by evaluation at points of $E$. Here **nuclear** means Grothendieck's condition of Definition C.2.4.1: $E$ is Hausdorff locally convex, and for every Hausdorff locally convex space $F$ the projective topology $\pi$ and the injective topology $\varepsilon$ on $E\otimes F$ coincide.
--
--   **Theorem.** If $E$ is nuclear, then every continuous seminorm on $E$ is dually dominated.
--
--   This is the forward half of the dual (transposed) form of the Grothendieck–Pietsch characterization of nuclear spaces by their canonical maps. Unlike the primal seminorm estimates, the dual form only involves functionals in $U_q^\circ$ and points of $E$, so it passes directly to Hausdorff quotients $E/V$: functionals on $E/V$ are the functionals on $E$ vanishing on $V$, and points of $E$ project to $E/V$.
--
--   **Formalization Note** The functionals are elements of `StrongDual ℂ E`; only their values are used. The sum is Lean's `tsum`; it converges because $c_n|f(y_n)|\le c_n$. The supremum is expressed pointwise, for each $x$ with $p(x)\le1$.
-- source:
--   A. Pietsch, Nuclear Locally Convex Spaces, Springer (1972), §3.2–3.3 (quasinuclear and nuclear maps, products of quasinuclear maps), §4.1–4.2 (Theorem 4.2.5: characterization of nuclear spaces by nuclear, quasinuclear and absolutely summing canonical maps) and §7.3 (equality of the projective and injective tensor topologies); H. H. Schaefer, Topological Vector Spaces (GTM 3, 2nd ed.), Ch. III, §7.2–7.5 (nuclear canonical maps $\widehat E_V\to\widehat E_U$, their transposes, and $\pi=\varepsilon$); F. Trèves, Topological Vector Spaces, Distributions and Kernels (1967), Ch. 50, Theorem 50.1. Used for Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, Definition C.2.4.1 (p. 685) and Lemma C.2.4.10 item 2 (p. 689), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem nuclear_dual_domination (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsNuclear E) (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (p : Seminorm ℂ E) (y : ℕ → E) (c : ℕ → ℝ),
      Continuous p ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n, q (y n) ≤ 1) ∧
      ∀ f : StrongDual ℂ E, (∀ x, ‖f x‖ ≤ q x) →
        ∀ x, p x ≤ 1 → ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖ := by sorry

end MasulloGRH
