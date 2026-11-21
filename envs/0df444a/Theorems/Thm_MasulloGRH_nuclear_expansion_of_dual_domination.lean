-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_expansion_of_dual_domination
-- name    : MasulloGRH.nuclear_expansion_of_dual_domination
-- status  : Proved
-- author  : @ijawdoij123
-- created : 2026-11-20T23:17:25.995686+00:00
-- url     : https://prove2.me/theorems/4ed914af-023a-4958-864c-02f811cb1703
-- title:
--   Nuclear spaces: dual domination yields nuclear expansions of canonical maps
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$ with continuous dual $E'$. For a continuous seminorm $q$ on $E$ let $U_q^\circ=\{f\in E' : |f(x)|\le q(x)\ \text{for all } x\}$. Call $q$ **dually dominated** if there are a continuous seminorm $p$, points $y_n\in E$ with $q(y_n)\le 1$ and reals $c_n\ge 0$ with $\sum_n c_n<\infty$ such that
--
--   $$|f(x)|\le\sum_{n=0}^\infty c_n\,|f(y_n)|\qquad\text{for all } f\in U_q^\circ \text{ and all } x \text{ with } p(x)\le 1 .$$
--
--   **Theorem.** Suppose every continuous seminorm on $E$ is dually dominated. Then for every continuous seminorm $q$ on $E$ the canonical map $\widetilde E_r\to\widetilde E_q$ is nuclear for some continuous seminorm $r$, with an expansion through points of $E$. That is, there exist a continuous seminorm $r$, points $y_n\in E$ with $q(y_n)\le1$, functionals $g_n\in E'$ with $|g_n(x)|\le r(x)$, and reals $c_n\ge0$ with $\sum_n c_n<\infty$, such that for every $x\in E$
--
--   $$q\Big(x-\sum_{n<N} c_n\,g_n(x)\,y_n\Big)\longrightarrow 0\qquad (N\to\infty).$$
--
--   This is the analytic core of the converse half of the Grothendieck–Pietsch characterization: it turns dual domination of seminorms, applied twice, into nuclear canonical maps with an explicit expansion. In particular it gives the quasinuclear estimate $q(x)\le\sum_n c_n|g_n(x)|$.
--
--   **Formalization Note** The hypothesis on $E$ is stated exactly as in `MasulloGRH.nuclear_of_dual_domination`. The partial sums are `Finset.range` sums and convergence is `Filter.Tendsto` to `0` in $\mathbb R$.
-- source:
--   A. Pietsch, Nuclear Locally Convex Spaces, Springer (1972), Ch. 2 (absolutely summing maps, Pietsch domination and factorization), Ch. 3 (quasinuclear and nuclear maps, products of quasinuclear maps) and Ch. 4 (characterization of nuclear spaces by nuclear and quasinuclear canonical maps and their duals); J. Diestel, H. Jarchow, A. Tonge, Absolutely Summing Operators, Cambridge Univ. Press (1995), Ch. 2 (p-summing operators, Pietsch factorization; 2-summing operators factor through Hilbert space and extend). Used for Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, Definition C.2.4.1 (p. 685) and Lemma C.2.4.10 (p. 689), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem nuclear_expansion_of_dual_domination (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E)
    (hdom : ∀ q : Seminorm ℂ E, Continuous q →
      ∃ (p : Seminorm ℂ E) (y : ℕ → E) (c : ℕ → ℝ),
        Continuous p ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n, q (y n) ≤ 1) ∧
        ∀ f : StrongDual ℂ E, (∀ x, ‖f x‖ ≤ q x) →
          ∀ x, p x ≤ 1 → ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖)
    (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ (r : Seminorm ℂ E) (y : ℕ → E) (g : ℕ → StrongDual ℂ E) (c : ℕ → ℝ),
      Continuous r ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧ (∀ n, q (y n) ≤ 1) ∧
      (∀ n x, ‖g n x‖ ≤ r x) ∧
      ∀ x, Filter.Tendsto
        (fun N : ℕ => q (x - ∑ n ∈ Finset.range N, ((c n : ℂ) * g n x) • y n))
        Filter.atTop (nhds 0) := by sorry

end MasulloGRH
