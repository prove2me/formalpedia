-- Prove2me | Theorems.Thm_MasulloGRH_bounded_scalar_expansion_of_domination
-- name    : MasulloGRH.bounded_scalar_expansion_of_domination
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-21T00:15:52.40208+00:00
-- url     : https://prove2.me/theorems/bc5ddb4e-9e16-4047-8e8b-a23abb914168
-- title:
--   Nuclear scalar expansion of bounded sets from nuclear domination
-- statement:
--   Let $G$ be a complete nuclear (Hausdorff, locally convex) space over $\mathbb C$ in which every bounded set is *nuclearly dominated*: for every bounded $D\subseteq G$ there are a bounded sequence $(y_n)$ in $G$ and summable weights $c_n\ge 0$ with
--   $$|f(x)|\le \sum_n c_n\,|f(y_n)|\qquad (f\in G'_\beta,\ x\in D).$$
--   Then every bounded set $B\subseteq G$ admits a nuclear scalar expansion: there are a null sequence $y_n\to 0$ in $G$, summable weights $c_n\ge 0$ and linear functionals $a_n$ on $\operatorname{span} B$ with $|a_n(x)|\le c_n$ for $x\in B$, such that
--   $$x=\sum_{n} a_n(x)\,y_n\qquad (x\in\operatorname{span}B),$$
--   the series converging in $G$.
--
--   Proof idea: applying the domination hypothesis twice (to $B$ and then to the bounded set $\{y_n\}$) shows that the restriction map $G'_\beta\to\ell^\infty(B)$ is a composition of two quasinuclear maps, hence nuclear (Pietsch); the coefficient functionals live in the strong bidual and are evaluations at points of a bounded set because $G$ is quasi-complete and nuclear (hence semi-reflexive); transposing and using completeness and Hahn–Banach gives the expansion, and a rescaling $y_n\mapsto y_n/\mu_n$ with $\mu_n\to\infty$, $\sum c_n\mu_n<\infty$ makes $y_n\to0$.
-- source:
--   A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, §C.2.4 (nuclear spaces: bounded sets in complete nuclear Fréchet / DF spaces); cf. A. Pietsch, Nuclear Locally Convex Spaces, §4.1–4.4 (composition of quasinuclear maps is nuclear).

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem bounded_scalar_expansion_of_domination (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hN : IsNuclear G)
    (hdom : ∀ D : Set G, Bornology.IsVonNBounded ℂ D →
      ∃ (y : ℕ → G) (c : ℕ → ℝ), Bornology.IsVonNBounded ℂ (Set.range y) ∧ (∀ n, 0 ≤ c n) ∧
        Summable c ∧ ∀ (f : StrongDual ℂ G), ∀ x ∈ D, ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖)
    (B : Set G) (hBb : Bornology.IsVonNBounded ℂ B) :
    ∃ (y : ℕ → G) (c : ℕ → ℝ) (a : ℕ → (Submodule.span ℂ B) →ₗ[ℂ] ℂ),
      Filter.Tendsto y Filter.atTop (nhds (0 : G)) ∧
      (∀ n, 0 ≤ c n) ∧ Summable c ∧
      (∀ n (x : Submodule.span ℂ B), (x : G) ∈ B → ‖a n x‖ ≤ c n) ∧
      ∀ x : Submodule.span ℂ B, HasSum (fun n => a n x • y n) (x : G) := by sorry

end MasulloGRH
