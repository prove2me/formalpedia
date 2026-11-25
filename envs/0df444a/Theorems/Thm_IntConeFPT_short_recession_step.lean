-- Prove2me | Theorems.Thm_IntConeFPT_short_recession_step
-- name    : IntConeFPT.short_recession_step
-- status  : Proved
-- author  : @ohnesorgefelix
-- created : 2026-11-25T08:43:22.451333+00:00
-- url     : https://prove2.me/theorems/bd3315e1-47ab-474f-a27a-6f991e6b4687
-- title:
--   Peeling a short integral recession direction from a large nonnegative lattice point
-- statement:
--   Let $A,b$ be integral with entries bounded in absolute value by $H\ge1$, and put $B=p(p+1)p!H^p$ in dimension $p\ge1$. Each nonnegative integral point of $Ax\le b$ whose coordinate sum exceeds $B$ splits as a feasible nonnegative integral point plus a nonzero nonnegative integral recession vector of coordinate sum at most $B$. One route is the vertex-and-ray representation of the pointed polyhedron (include nonnegativity among the rows). Cramer’s rule bounds vertex coordinates and primitive ray coordinates by $p!H^p$. Use conic Carathéodory to keep at most $p$ rays: if every ray multiplier were less than one the coordinate sum would be at most $B$. Otherwise subtract one primitive ray.
-- source:
--   Jansen, Ohnesorge and Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, https://arxiv.org/abs/2609.31328, §3.6, equation (3.4), and Appendix B, proof of Lemma 15. Auxiliary polyhedral formulation of the small-count argument, rather than a separately stated result of the paper.

import Mathlib

theorem IntConeFPT.short_recession_step {p m H : ℕ} (hp : 1 ≤ p) (hH : 1 ≤ H)
    (A : Matrix (Fin m) (Fin p) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ H) (hb : ∀ i, |b i| ≤ H)
    (z : Fin p → ℕ) (hz : ∀ i, ∑ j, A i j * (z j : ℤ) ≤ b i)
    (hlarge : p * (p + 1) * p.factorial * H ^ p < ∑ j, z j) :
    ∃ y r : Fin p → ℕ, z = y + r ∧
      (∀ i, ∑ j, A i j * (y j : ℤ) ≤ b i) ∧
      (∀ i, ∑ j, A i j * (r j : ℤ) ≤ 0) ∧
      0 < ∑ j, r j ∧ ∑ j, r j ≤ p * (p + 1) * p.factorial * H ^ p := by sorry
