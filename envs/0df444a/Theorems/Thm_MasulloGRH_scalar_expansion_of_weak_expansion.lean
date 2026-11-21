-- Prove2me | Theorems.Thm_MasulloGRH_scalar_expansion_of_weak_expansion
-- name    : MasulloGRH.scalar_expansion_of_weak_expansion
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-21T00:20:27.67177+00:00
-- url     : https://prove2.me/theorems/11d643ea-0071-4375-9a2f-cf544a6e1366
-- title:
--   From a weak nuclear representation to a convergent scalar expansion
-- statement:
--   Let $G$ be a complete Hausdorff locally convex space over $\mathbb C$, $B\subseteq G$ a set, $(w_n)$ a bounded sequence in $G$, $Y_n\in G'$ continuous linear functionals with $|Y_n(x)|\le 1$ for $x\in B$, and $c_n\ge0$ summable weights. Assume the weak expansion
--   $$f(x)=\sum_n c_n\,Y_n(x)\,f(w_n)\qquad(f\in G',\ x\in B).$$
--
--   Then there are a null sequence $y_n\to0$ in $G$, summable weights $c'_n\ge0$ and linear functionals $a_n$ on $\operatorname{span}B$ with $|a_n(x)|\le c'_n$ for $x\in B$ such that
--   $$x=\sum_n a_n(x)\,y_n\qquad(x\in\operatorname{span}B),$$
--   the series converging (unconditionally) in $G$.
--
--   This upgrades a weak, coefficient-wise representation to a genuine convergent nuclear expansion, using completeness of $G$, the Hahn–Banach separation of points, and a rescaling $w_n\mapsto w_n/\mu_n$ by weights $\mu_n\to\infty$ with $\sum_n c_n\mu_n<\infty$.
-- source:
--   A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, §C.2.4 (bounded sets in complete nuclear spaces); cf. A. Pietsch, Nuclear Locally Convex Spaces, §3.3 and §4.1 (composition of two quasinuclear maps is nuclear; semi-reflexivity of quasi-complete nuclear spaces).

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem scalar_expansion_of_weak_expansion (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hL : IsHLCS G)
    (B : Set G) (w : ℕ → G) (Y : ℕ → StrongDual ℂ G) (c : ℕ → ℝ)
    (hw : Bornology.IsVonNBounded ℂ (Set.range w)) (hc0 : ∀ n, 0 ≤ c n) (hc : Summable c)
    (hY : ∀ n, ∀ x ∈ B, ‖Y n x‖ ≤ 1)
    (hrep : ∀ (f : StrongDual ℂ G), ∀ x ∈ B,
      HasSum (fun n => (c n : ℂ) * Y n x * f (w n)) (f x)) :
    ∃ (y : ℕ → G) (c : ℕ → ℝ) (a : ℕ → (Submodule.span ℂ B) →ₗ[ℂ] ℂ),
      Filter.Tendsto y Filter.atTop (nhds (0 : G)) ∧
      (∀ n, 0 ≤ c n) ∧ Summable c ∧
      (∀ n (x : Submodule.span ℂ B), (x : G) ∈ B → ‖a n x‖ ≤ c n) ∧
      ∀ x : Submodule.span ℂ B, HasSum (fun n => a n x • y n) (x : G) := by sorry

end MasulloGRH
