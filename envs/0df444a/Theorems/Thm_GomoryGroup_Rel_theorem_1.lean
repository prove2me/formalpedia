-- Prove2me | Theorems.Thm_GomoryGroup_Rel_theorem_1
-- name    : GomoryGroup.Rel.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:30:54.447662+00:00
-- url     : https://prove2.me/theorems/4be13c2f-8b8a-4ff0-b63f-e508f1967dab
-- title:
--   THEOREM 1, p. 261 — for b ∈ K^B(l(D − 1)), z₂(b) = z₁(b) + φ^B(b), x(b) = (B⁻¹(b − Ny^B(b)), y^B(b)) is optimal, φ^B and y^B are periodic
-- statement:
--   **Setting.** Let $A=(B,N)$ be an integer $m\times(m+n)$ matrix rearranged so that $B=(\alpha_1,\dots,\alpha_m)$ is a nonsingular basis and $N=(\alpha_{m+1},\dots,\alpha_{m+n})$ (column $j$ of $N$ is $\alpha_{m+1+j}$, $j=0,\dots,n-1$). Assume every unit vector of $\mathbb Z^m$ is a column of $A$ (the paper's $A=(A',I)$). Let $c=(c_B,c_N)$ be a real cost vector such that $B$ is an optimal basis, i.e. every relative cost $c^*_{m+1+j}=c_{m+1+j}-c_BB^{-1}\alpha_{m+1+j}$ is $\le0$. Let
--   $$l=\max_{i=m+1,\dots,m+n}\|\alpha_i\|,\qquad D=|\det B|,$$
--   and let $b\in\mathbb Z^m$ lie in the reduced cone $K^B(l(D-1))$. P1 is $\max\{cx: Ax=b, x\ge0\}$, P2 is P1 with $x$ integer, and (4) is the group problem $\max\sum_i c^*_{i+m}y_i$ subject to $\sum_i\bar\alpha_{i+m}y_i=\bar b$ in $M(I)/M(B)$, $y\in\mathbb N^n$, whose value is $\varphi^B(b)$.
--
--   **Theorem 1.** Then
--
--   1. P1 and (4) attain their maxima $z_1(b)$ and $\varphi^B(b)$;
--   2. the maximum $z_2(b)$ of P2 is attained and
--   $$z_2(b)=z_1(b)+\varphi^B(b);\qquad (2)$$
--   3. (4) has an optimal solution $y^B(b)$ with $\sum_i y^B_i(b)\le D-1$;
--   4. for every such optimal solution $y=y^B(b)$, the vector
--   $$x(b)=(x_B(b),x_N(b))=(B^{-1}(b-Ny^B(b)),\,y^B(b))\qquad (3)$$
--   is integral, nonnegative and optimal for P2;
--   5. (4) is $m$-periodic in $b$: for $i=1,\dots,m$, (4) with right-hand side $b+\alpha_i$ has the same feasible solutions as with $b$, so $\varphi^B(b+\alpha_i)=\varphi^B(b)$ and $y^B(b+\alpha_i)=y^B(b)$.
--
--   The theorem says that for right-hand sides deep inside the cone of the LP-optimal basis, the integer program is solved by the LP solution corrected by a problem over a finite abelian group, and the correction depends only on $b$ modulo the lattice of the basis.
--
--   **Formalization Note** The standing assumptions of pp. 260–262 ($\det B\neq0$, $A=(A',I)$, $B$ optimal) are hypotheses. Optimal values are greatest elements of the sets of objective values; parts 1–3 assert that they exist. $y^B(b)$ is the optimal solution of (4) that the LEMMA and the dynamic program of p. 264 produce, which has $\sum_i y_i\le D-1$; part 4 is stated for every optimal $y$ with that bound, because an arbitrary optimal $y$ (with zero-cost cycles) can make $x_B$ negative. The group problem is written as $b-Ny\in B\mathbb Z^m$; $x_B=B^{-1}(b-Ny)$ is stated as $Bx_B=b-Ny$ with $x_B\in\mathbb N^m$. The norm is Euclidean, and $K^B(d)$ is the set of points whose closed ball of radius $d$ lies in $K^B=\{\beta:B^{-1}\beta\ge0\}$. $D-1$ is natural-number subtraction ($D\ge1$).
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), p. 261, THEOREM 1, (2), (3); p. 262, (4)

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem theorem_1 {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ)
    (hB : B.det ≠ 0) (hI : HasUnitColumns B N) (hopt : ∀ j, reducedCost B N cB cN j ≤ 0)
    (hb : (fun i => (b i : ℝ)) ∈ reducedCone B (ell N * ((detD B : ℝ) - 1))) :
    -- the optimal values z₁(b) of P1 and φ^B(b) of (4) exist
    ((∃ z₁ : ℝ, IsGreatest (lpValues B N cB cN (fun i => (b i : ℝ))) z₁) ∧
      (∃ φ : ℝ, IsGreatest (groupValues B N cB cN b) φ)) ∧
    -- (2): z₂(b) = z₁(b) + φ^B(b)
    (∀ z₁ φ : ℝ, IsGreatest (lpValues B N cB cN (fun i => (b i : ℝ))) z₁ →
      IsGreatest (groupValues B N cB cN b) φ → IsGreatest (ipValues B N cB cN b) (z₁ + φ)) ∧
    -- y^B(b): an optimal solution of (4) with Σ y_i ≤ D − 1
    (∃ y : Fin n → ℕ, IsGroupOptimal B N cB cN b y ∧ ∑ j, y j ≤ detD B - 1) ∧
    -- (3): (B⁻¹(b − N y), y) is integral, nonnegative and optimal for P2
    (∀ y : Fin n → ℕ, IsGroupOptimal B N cB cN b y → ∑ j, y j ≤ detD B - 1 →
      ∃ xB : Fin m → ℕ, B *ᵥ (fun i => (xB i : ℤ)) = b - N *ᵥ (fun j => (y j : ℤ)) ∧
        IsIPOptimal B N cB cN b xB y) ∧
    -- m-periodicity: (4) for b + α_i is (4) for b
    (∀ i : Fin m,
      (∀ y : Fin n → ℕ, IsGroupFeasible B N (b + fun r => B r i) y ↔ IsGroupFeasible B N b y) ∧
        groupValues B N cB cN (b + fun r => B r i) = groupValues B N cB cN b) := by sorry

end GomoryGroup.Rel
