-- Prove2me | Theorems.Thm_MasulloGRH_quasinuclear_comp_nuclear_expansion
-- name    : MasulloGRH.quasinuclear_comp_nuclear_expansion
-- status  : Proved
-- author  : @ijawdoij123
-- created : 2026-11-20T23:19:18.945362+00:00
-- url     : https://prove2.me/theorems/f3a30b31-b33a-4712-8152-d84bce94066d
-- title:
--   Product of two quasi-nuclear canonical maps is nuclear
-- statement:
--   Let $E$ be a complex vector space with a topology, and let $E'$ be its space of continuous linear functionals. For seminorms $p,r$ on $E$ say that $p$ is **quasi-nuclearly dominated by $r$** if there are $f_n\in E'$ and reals $a_n\ge0$ with $\sum_n a_n<\infty$ such that
--   $$|f_n(x)|\le r(x)\quad\text{and}\quad p(x)\le\sum_{n=0}^\infty a_n|f_n(x)|\qquad(n\ge0,\ x\in E);$$
--   equivalently, the canonical map $E_r\to E_p$ between the associated seminormed spaces is quasi-nuclear.
--
--   **Theorem.** Let $q,r,s$ be seminorms on $E$ such that $q$ is quasi-nuclearly dominated by $r$ and $r$ is quasi-nuclearly dominated by $s$. Then the canonical map $E_s\to\widehat E_q$ is nuclear, with a nuclear representation whose vectors are points of $E$: there exist $h_n\in E'$, $y_n\in E$ and reals $c_n\ge0$ with $\sum_n c_n<\infty$ such that $|h_n(x)|\le s(x)$, $q(y_n)\le1$ for all $n$, and for every $x\in E$
--   $$\lim_{N\to\infty} q\Big(x-\sum_{n=0}^{N-1}c_n\,h_n(x)\,y_n\Big)=0 .$$
--
--   This is the seminorm form of the classical fact that the product of two quasi-nuclear maps between normed spaces is nuclear. Applied to the canonical maps $E_s\to E_r\to E_q$ of a locally convex space, it turns quasi-nuclear canonical maps into nuclear ones, which is how condition (2) of the characterization of nuclear spaces (nuclear canonical maps $\widehat E_V\to\widehat E_U$) is reached from quasi-nuclear domination; transposing the expansion gives estimates for functionals $f$ with $|f|\le q$ in terms of the values $f(y_n)$.
--
--   **Formalization Note** The vectors of a nuclear representation of $E_s\to\widehat E_q$ lie a priori in the completion $\widehat E_q$; the statement replaces them by points of $E$ (each vector of the completion is the sum of a $q$-absolutely convergent series of points of $E$, and the resulting double series is re-enumerated), and expresses convergence in $\widehat E_q$ as convergence for the seminorm $q$. The dominations are stated with Lean's `tsum`; the series converge since $a_n|f_n(x)|\le a_n r(x)$. The scalars $c_n$ are real and enter as complex numbers. No continuity of $q,r,s$ is needed.
-- source:
--   A. Pietsch, Nuclear Locally Convex Spaces, Springer (1972), §3.3 (quasinuclear mappings in normed spaces) and §3.4 (products of quasinuclear and absolutely summing mappings in normed spaces). Nuclear operators as in A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, eq. (C.2.4.2) (pp. 685–686, after [Scha, Ch. III, Rem. to 7.1]), used for Theorem C.2.4.2 (1)⇔(2) (p. 686, nuclear canonical maps of local Banach spaces), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf; H. H. Schaefer, Topological Vector Spaces, Ch. III, §7.1–7.2.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open Filter Topology

namespace MasulloGRH

universe u

theorem quasinuclear_comp_nuclear_expansion (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (q r s : Seminorm ℂ E)
    (f : ℕ → StrongDual ℂ E) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (has : Summable a)
    (hf : ∀ n x, ‖f n x‖ ≤ r x) (hqr : ∀ x, q x ≤ ∑' n, a n * ‖f n x‖)
    (g : ℕ → StrongDual ℂ E) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hbs : Summable b)
    (hg : ∀ n x, ‖g n x‖ ≤ s x) (hrs : ∀ x, r x ≤ ∑' n, b n * ‖g n x‖) :
    ∃ (h : ℕ → StrongDual ℂ E) (y : ℕ → E) (c : ℕ → ℝ),
      (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n x, ‖h n x‖ ≤ s x) ∧ (∀ n, q (y n) ≤ 1) ∧
      ∀ x, Tendsto (fun N => q (x - ∑ n ∈ Finset.range N, ((c n : ℂ) * h n x) • y n)) atTop (𝓝 0) := by sorry

end MasulloGRH
