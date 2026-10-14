-- Prove2me | Theorems.Thm_MonotoneMVJump_Compare_theorem_7
-- name    : MonotoneMVJump.Compare.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:17.737371+00:00
-- url     : https://prove2.me/theorems/c60b4c6e-695f-4f8e-a66f-143df9a36f3e
-- title:
--   Theorem 7 — $c^*(A)=(A-x)\frac{E[R_T]}{1-E[R_T]}$ and $A^*+c^*(A^*)=x+\frac1\theta\frac{1-E[R_T]}{\mathrm{Var}[R_T]}$
-- statement:
--   Assume the standing market assumptions, the Conditions of Proposition 1, a solution $G$ of (20), initial data $t<T$, $z$ with factor path $Z$, $\theta>0$ and $x\in\mathbb R$. Let $R$ solve (38) with $\mathbb E[R_T]\ne1$ and $\mathrm{Var}[R_T]>0$. Put
--   $$c^*(A)=(A-x)\frac{\mathbb E_{z,t}[R_T]}{1-\mathbb E_{z,t}[R_T]} .$$
--   For a target $D$, a "(37)-pair" is an admissible $\pi\in\mathcal B_{x,z,t}$ with wealth $X$ following (37) with target $D$ on $[t,T]$. Then:
--   1. for every $D$ a (37)-pair exists;
--   2. for every $A$, $c$ and (37)-pair with target $A+c$: $\mathbb E[X_T]=A$ if and only if $c=c^*(A)$;
--   3. a number $A^*$ maximizes $A\mapsto U_\theta(X^{\pi^*(A+c^*(A))}_T)$ if and only if
--   $$A^*+c^*(A^*)=x+\frac1\theta\cdot\frac{1-\mathbb E_{z,t}[R_T]}{\mathrm{Var}_{z,t}[R_T]}.$$
--   Here "maximizes" means $U_\theta(X_T)\le U_\theta(X'_T)$ for every (37)-pair $X$ with target $A+c^*(A)$, every $A$, and every (37)-pair $X'$ with target $A^*+c^*(A^*)$.
--
--   This solves the outer optimization of the Lagrangian embedding and identifies the optimal target $D^*$ of the MV problem.
--
--   **Formalization Note** The paper divides by $1-\mathbb E[R_T]$ and $\mathrm{Var}[R_T]$; the hypotheses $\mathbb E[R_T]\ne1$ and $\mathrm{Var}[R_T]>0$ make this explicit. $c^*(A)$ and $A^*$ are defined in the text before the theorem (pp. 20, 22), and are characterized here, not assumed. Existence of the (37)-pairs is part of the statement, so the maximization is not vacuous.
-- source:
--   Li, Liang & Pang, Comparison Between Mean-Variance and Monotone Mean-Variance Preferences Under Jump Diffusion and Stochastic Factor Model, arXiv:2211.14473v2, p. 23, Theorem 7, (38); c*(A), A* defined pp. 20, 22

import Mathlib
import Definitions.Def_MonotoneMVJump_Compare_PDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MonotoneMVJump.Compare

/-- Theorem 7 (p. 23): with `R` the solution of (38) and `c*(A) = (A − x) E[R_T]/(1 − E[R_T])`:
(1) for every target `D` a feedback pair of (37) exists in `ℬ_{x,z,t}`;
(2) for the (37)-pair with target `A + c`, `E[X_T] = A` if and only if `c = c*(A)`;
(3) `A*` maximizes `A ↦ U_θ(X^{π*(A+c*(A))}_T)` if and only if
`A* + c*(A*) = x + (1/θ)(1 − E[R_T])/Var[R_T]`. -/
theorem theorem_7 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (hP1 : PropOneConditions M) (G : ℝ → ℝ → ℝ) (hG : IsGSolution M G)
    (t : ℝ≥0) (ht : t < M.T) (z : ℝ) (Z : ℝ≥0 → Ω → ℝ) (hZ : M.IsFactor t z Z)
    (θ : ℝ) (hθ : 0 < θ) (x : ℝ) (R : ℝ≥0 → Ω → ℝ) (hR : IsRProcess M G t Z R)
    (hER : ∫ ω, R M.T ω ∂M.P ≠ 1) (hVar : 0 < variance (R M.T) M.P) :
    let ER := ∫ ω, R M.T ω ∂M.P
    let cstar : ℝ → ℝ := fun A => (A - x) * (ER / (1 - ER))
    let Pair : ℝ → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop := fun D π X =>
      (∀ᵐ ω ∂M.P, ∀ s : ℝ≥0, t ≤ s → s ≤ M.T → π s ω = problem3Strategy M G D Z X s ω) ∧
        M.AdmB t x Z π X
    (∀ D : ℝ, ∃ π X : ℝ≥0 → Ω → ℝ, Pair D π X) ∧
      (∀ (A c : ℝ) (π X : ℝ≥0 → Ω → ℝ), Pair (A + c) π X →
        (∫ ω, X M.T ω ∂M.P = A ↔ c = cstar A)) ∧
      ∀ Astar : ℝ,
        (∀ (A : ℝ) (π X π' X' : ℝ≥0 → Ω → ℝ), Pair (A + cstar A) π X →
            Pair (Astar + cstar Astar) π' X' → M.mvU θ (X M.T) ≤ M.mvU θ (X' M.T)) ↔
          Astar + cstar Astar = x + 1 / θ * ((1 - ER) / variance (R M.T) M.P) := by sorry

end MonotoneMVJump.Compare
