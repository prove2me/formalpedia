-- Prove2me | Theorems.Thm_MFIrrev_Equilibrium_theorem_4_1_step_1
-- name    : MFIrrev.Equilibrium.theorem_4_1_step_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:06.398265+00:00
-- url     : https://prove2.me/theorems/66ce1c78-6248-4265-aeb9-ef3ea7e53aab
-- title:
--   Proof of Theorem 4.1, Step 1, p. 23 — v^Q(x,i) is decreasing in Q, hence so are the free boundaries aᵢ(Q)
-- statement:
--   Assume the standing conditions of §2 and Assumption 2.1. For $Q\in(0,\infty)^2$ write $v^Q$ for the value function (4.13) of the stopping problem with $\eta_i=\varphi_i+\zeta_iQ_i^{-\alpha}$. If $Q\le Q'$ componentwise, then
--
--   1. $v^{Q'}(x,i)\le v^{Q}(x,i)$ for all $x>0$ and $i\in\{1,2\}$;
--   2. the free boundaries are decreasing: if $a,a'\in[0,\infty)^2$ satisfy $\{x>0: v^Q(x,j)<\kappa\}=(a_j,\infty)$ and $\{x>0: v^{Q'}(x,j)<\kappa\}=(a'_j,\infty)$ for both $j$, then $a'_j\le a_j$, i.e. with $a_i(Q)=\inf\{x>0:v^Q(x,i)<\kappa\}$, $Q\mapsto a_i(Q)$ is decreasing in each coordinate.
--
--   This monotonicity is the input of the uniqueness argument for the mean-field fixed point.
--
--   **Formalization Note.** "Decreasing" is weak monotonicity under the componentwise order on $(0,\infty)^2$; monotonicity in $Q_1$ and in $Q_2$ separately is the special case where one coordinate is fixed. The continuity claim of Step 1 (via the implicit function theorem on (4.23)) is not part of this statement. Regimes are `Fin 2` (index `0` = regime 1).
-- source:
--   Aïd, Basei & Ferrari, A Stationary Mean-Field Equilibrium Model of Irreversible Investment in a Two-Regime Economy, arXiv:2305.00541v1, p. 23, proof of Theorem 4.1, Step 1 (monotonicity part)

import Mathlib
import Definitions.Def_MFIrrev_Equilibrium_StoppingProblem

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MFIrrev.Equilibrium

/-- Proof of Theorem 4.1, Step 1, Aïd–Basei–Ferrari p. 23 (monotonicity part). Regime index `0` is
the paper's regime 1. If `Q ≤ Q'` componentwise, then `v^{Q'}(x, i) ≤ v^Q(x, i)` for all `x > 0` and
`i`, and the free boundaries decrease: any thresholds `a`, `a'` describing the continuation regions
`{v^Q(·, j) < κ} = (a_j, ∞)` and `{v^{Q'}(·, j) < κ} = (a'_j, ∞)` satisfy `a'_j ≤ a_j`. -/
theorem theorem_4_1_step_1 (m : Params) (hδ : 0 < m.δ) (hσ : ∀ j, 0 < m.σ j) (hp : ∀ j, 0 < m.p j ∧ m.p j < 1)
    (hρ : 0 < m.ρ) (hc : 0 < m.c) (hκ : 0 < m.κ) (hφ : ∀ j, 0 < m.φ j) (hζ : ∀ j, 0 < m.ζ j)
    (hα0 : 0 < m.α) (hα1 : m.α < 1) (hφρδ : ∀ j, m.ρ + m.δ < m.φ j)
    (hA21 : 2 * max (m.σ 0 ^ 2) (m.σ 1 ^ 2) < m.ρ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (S : Setting Ω) (hS : IsSetting m P S)
    (Q Q' : Fin 2 → ℝ) (hQ : ∀ j, 0 < Q j) (hQQ' : ∀ j, Q j ≤ Q' j) :
    (∀ x : ℝ, 0 < x → ∀ i : Fin 2, vStop m P S Q' x i ≤ vStop m P S Q x i) ∧
    ∀ a a' : Fin 2 → ℝ, (∀ j, 0 ≤ a j) → (∀ j, 0 ≤ a' j) →
      (∀ j, ∀ y : ℝ, 0 < y → (vStop m P S Q y j < m.κ ↔ a j < y)) →
      (∀ j, ∀ y : ℝ, 0 < y → (vStop m P S Q' y j < m.κ ↔ a' j < y)) →
      ∀ j, a' j ≤ a j := by sorry

end MFIrrev.Equilibrium
