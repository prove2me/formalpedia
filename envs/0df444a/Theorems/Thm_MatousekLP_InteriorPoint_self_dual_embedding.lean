-- Prove2me | Theorems.Thm_MatousekLP_InteriorPoint_self_dual_embedding
-- name    : MatousekLP.InteriorPoint.self_dual_embedding
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T11:45:08.035053+00:00
-- url     : https://prove2.me/theorems/e63869c5-43a1-47ec-a182-a9545a5c6a57
-- title:
--   Lemma 7.2.3 — the self-dual program (SD) and its strictly complementary optima
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb{R}^m$, $c\in\mathbb{R}^n$, $k=n+m+1$, and let
--   $$M_0=\begin{pmatrix}0 & A & -b\\ -A^{T} & 0 & c\\ b^{T} & -c^{T} & 0\end{pmatrix},\quad r=\mathbf 1+M_0\mathbf 1,\quad M=\begin{pmatrix}M_0 & -r\\ r^{T} & 0\end{pmatrix},\quad q=(0,\dots,0,k+1)\in\mathbb{R}^{k+1}.$$
--   Consider the linear program
--
--   $$\text{(SD)}\qquad \text{maximize } -q^{T}v \ \text{ subject to } Mv\le q,\ v\ge 0,$$
--
--   in $v=(u,\vartheta)$ with $u=(y,x,\tau)\in\mathbb{R}^{k}$, and write $z=q-Mv$ for its slacks. Then:
--
--   1. (SD) has a feasible solution, and its objective is bounded from above on the feasible set;
--   2. every optimal solution $v=(u,\vartheta)$ of (SD) has $\vartheta=0$, and its $u$-part $(y,x,\tau)$ is a solution of the Goldman–Tucker system (GTS) $Ax-\tau b\le 0$, $-A^{T}y+\tau c\le 0$, $b^{T}y-c^{T}x\le 0$, $x,y\ge 0$, $\tau\ge 0$;
--   3. if moreover $v$ is strictly complementary (for each coordinate $j$, $v_j>0$ or $z_j>0$), then the resulting solution of (GTS) has $\tau>0$ or $\rho=c^{T}x-b^{T}y>0$.
--
--   Together with Lemma 7.2.2, this reduces solving (7.7) to finding a strictly complementary optimal solution of (SD), a program with an explicit interior starting point.
--
--   **Formalization Note** $u$ is indexed by `Fin m ⊕ Fin n ⊕ Unit` and $v$ by `(Fin m ⊕ Fin n ⊕ Unit) ⊕ Unit`; `uY`, `uX`, `uTau`, `vU`, `vTheta` extract $y$, $x$, $\tau$, $u$, $\vartheta$. Optimality and boundedness are stated against every feasible point.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, §7.2, p. 128, Lemma 7.2.3 (with M_0, r, M p. 127 and q, (SD) p. 128)

import Mathlib
import Definitions.Def_MatousekLP_InteriorPoint_SelfDual

namespace MatousekLP.InteriorPoint

open Matrix

/-- Lemma 7.2.3 (Matoušek & Gärtner, p. 128). The linear program
(SD) `maximize −qᵀv subject to Mv ≤ q, v ≥ 0` built from `A, b, c` is feasible and bounded,
every optimal solution `v = (u, ϑ)` has `ϑ = 0`, and hence its `u`-part `u = (y, x, τ)` is a
solution of the Goldman–Tucker system (GTS). Moreover, every strictly complementary optimal
solution yields a solution of (GTS) with `τ > 0` or `ρ > 0`. -/
theorem self_dual_embedding {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) :
    (∃ v : VIdx m n → ℝ, IsSDFeasible A b c v) ∧
    IsSDBoundedAbove A b c ∧
    (∀ v : VIdx m n → ℝ, IsSDOptimal A b c v →
        vTheta v = 0 ∧ IsGTSSolution A b c (uX (vU v)) (uY (vU v)) (uTau (vU v))) ∧
    (∀ v : VIdx m n → ℝ, IsSDOptimal A b c v → IsStrictlyComplementary A b c v →
        0 < uTau (vU v) ∨ 0 < gtsSlack b c (uX (vU v)) (uY (vU v))) := by sorry

end MatousekLP.InteriorPoint
