-- Prove2me | Theorems.Thm_MasulloGRH_bounded_weak_nuclear_repr_of_domination
-- name    : MasulloGRH.bounded_weak_nuclear_repr_of_domination
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-21T00:20:23.094251+00:00
-- url     : https://prove2.me/theorems/cf181640-29f1-4082-aa0b-7b5d624b3cde
-- title:
--   Weak nuclear representation of bounded sets from nuclear domination
-- statement:
--   Let $G$ be a complete nuclear (Hausdorff, locally convex) space over $\mathbb C$ in which every bounded set is nuclearly dominated: for each bounded $D\subseteq G$ there are a bounded sequence $(y_n)$ and summable weights $c_n\ge0$ with $|f(x)|\le\sum_n c_n|f(y_n)|$ for all $f\in G'_\beta$ and $x\in D$.
--
--   Then for every bounded $B\subseteq G$ there are a bounded sequence $(w_n)$ in $G$, continuous linear functionals $Y_n\in G'$ with $\sup_{x\in B}|Y_n(x)|\le 1$, and summable weights $c_n\ge 0$ such that
--   $$f(x)=\sum_{n} c_n\,Y_n(x)\,f(w_n)\qquad(f\in G',\ x\in B),$$
--   the series being absolutely convergent.
--
--   In other words, the restriction map $G'_\beta\to\ell^\infty(B)$ is nuclear and its coefficient functionals are evaluations at the points of a bounded set. This is the dual (weak) form of the statement that bounded sets of such spaces are nuclearly embedded.
-- source:
--   A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, §C.2.4 (bounded sets in complete nuclear spaces); cf. A. Pietsch, Nuclear Locally Convex Spaces, §3.3 and §4.1 (composition of two quasinuclear maps is nuclear; semi-reflexivity of quasi-complete nuclear spaces).

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem bounded_weak_nuclear_repr_of_domination (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hN : IsNuclear G)
    (hdom : ∀ D : Set G, Bornology.IsVonNBounded ℂ D →
      ∃ (y : ℕ → G) (c : ℕ → ℝ), Bornology.IsVonNBounded ℂ (Set.range y) ∧ (∀ n, 0 ≤ c n) ∧
        Summable c ∧ ∀ (f : StrongDual ℂ G), ∀ x ∈ D, ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖)
    (B : Set G) (hBb : Bornology.IsVonNBounded ℂ B) :
    ∃ (w : ℕ → G) (Y : ℕ → StrongDual ℂ G) (c : ℕ → ℝ),
      Bornology.IsVonNBounded ℂ (Set.range w) ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧
      (∀ n, ∀ x ∈ B, ‖Y n x‖ ≤ 1) ∧
      ∀ (f : StrongDual ℂ G), ∀ x ∈ B, HasSum (fun n => (c n : ℂ) * Y n x * f (w n)) (f x) := by sorry

end MasulloGRH
