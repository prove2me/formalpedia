-- Prove2me | Theorems.Thm_LemkeLCP_Existence_theorem_4
-- name    : LemkeLCP.Existence.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:04:48.919857+00:00
-- url     : https://prove2.me/theorems/f2d1b156-3510-4cc4-bc43-93cb099bfa8a
-- title:
--   Theorem 4, p. 7 — non-degenerate Z, uᵀMu ≥ 0 and uᵀMu = 0 ⇒ Mu + Mᵀu = 0 for u ≥ 0: a non-empty Z has an equilibrium point
-- statement:
--   Let $M$ be a real square matrix of order $n$ and $q\in\mathbb R^n$, and let
--   $$Z=\{z\in\mathbb R^n : z\ge 0,\ w=Mz-q\ge 0\}.$$
--   Suppose that $Z$ is non-degenerate (Def. 3), and that $M$ has the property that for every $u\ge 0$:
--
--   1. $u^{\mathsf T}Mu\ge 0$, and
--   2. $u^{\mathsf T}Mu=0$ implies $Mu+M^{\mathsf T}u=0$.
--
--   Then, if $Z$ is non-empty, it has an equilibrium point: there is $z\ge0$ with $w=Mz-q\ge0$ and
--   $$z^{\mathsf T}w=0 .$$
--
--   In current terminology: a feasible linear complementarity problem $\mathrm{LCP}(q,M)$ with a copositive-plus matrix $M$ is solvable. This is the main result of the paper; its proof, by an adjacent-extreme-point path on an augmented set, is the origin of Lemke's complementary pivoting algorithm. It contains the case where $z^{\mathsf T}Mz\ge0$ for all $z$ (convex quadratic programming) and the case $M>0$.
--
--   **Formalization Note** Non-degeneracy requires, for every $z\in\mathbb R^n$, that the columns of $N(z)$ (the columns of $(M^{\mathsf T},I)$ kept by the zero pattern of $(w,z)$) be linearly independent. The hypotheses are exactly those printed; no assumption on the augmented sets $Z^*$, $Z^{**}$ is added.
-- source:
--   Lemke, Bimatrix equilibrium points and mathematical programming, hal-01885823v1, p. 7, Theorem 4, (i), (ii), (21)

import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting
open Matrix

namespace LemkeLCP.Existence

theorem theorem_4 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (hnd : NonDegenerate M q) (hM : CopositivePlus M) (hZ : (Z M q).Nonempty) :
    ∃ z : ι → ℝ, IsEquilibriumPoint M q z := by sorry

end LemkeLCP.Existence
