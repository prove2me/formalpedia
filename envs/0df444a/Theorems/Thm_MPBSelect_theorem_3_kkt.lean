-- Prove2me | Theorems.Thm_MPBSelect_theorem_3_kkt
-- name    : MPBSelect.theorem_3_kkt
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:47.163774+00:00
-- url     : https://prove2.me/theorems/cd78c6c0-c16c-48e4-8e74-95288be8e460
-- title:
--   Proof of Theorem 3, p.ec9 — the KKT system (EC.17)–(EC.21) is necessary and sufficient for optimality (corrected: (EC.20) only at $\theta_b$ carrying a pair of $\Xi$)
-- statement:
--   Consider an MPB problem (with $k\ge2$, $p_b>0$, $\sum_bp_b=1$, assumptions (i)–(ii) and $\lambda>0$), and let $B_\Xi$ be the set of parameters at which $\Xi$ has a pair. Let $\boldsymbol\alpha$ be feasible for (20) with the properties that the proof has established for optimal allocations at this point:
--
--   1. $\alpha_{i^*}(\theta_b)=0$ for all $\theta_b\in\Theta^c_{i^*}$, and $\alpha_{i^b}(\theta_b)=0$ for $\theta_b\notin B_\Xi$;
--   2. $\alpha_i(\theta_b)>0$ for $(i,\theta_b)\in\Xi$, and $\alpha_{i^b}(\theta_b)>0$ for $\theta_b\in B_\Xi$.
--
--   Then $\boldsymbol\alpha$ is optimal for (20) if and only if there are reals $C,\gamma$ and multipliers $\rho=\{\rho_i(\theta_b)\}$ such that $C\le W_i(\theta_b)G_i(\theta_b)$ for all $(i,\theta_b)\in\Xi$ and
--   $$
--   \begin{aligned}
--   &\rho_i(\theta_b)\ge0, && (i,\theta_b)\in\Xi, &&\text{(EC.17)}\\
--   &-1+\textstyle\sum_{(i,\theta_b)\in\Xi}\rho_i(\theta_b)=0, && &&\text{(EC.18)}\\
--   &-\rho_i(\theta_b)W_i(\theta_b)\,\partial_iG_i(\theta_b)+\gamma=0, && (i,\theta_b)\in\Xi, &&\text{(EC.19)}\\
--   &-\textstyle\sum_{i\ne i^b,i^*}\rho_i(\theta_b)W_i(\theta_b)\,\partial_{i^b}G_i(\theta_b)+\gamma=0, && \theta_b\in B_\Xi, &&\text{(EC.20)}\\
--   &\rho_i(\theta_b)\big(C-W_i(\theta_b)G_i(\theta_b)\big)=0, && (i,\theta_b)\in\Xi, &&\text{(EC.21)}
--   \end{aligned}
--   $$
--   where $\partial_iG_i(\theta_b)=G_i(\theta_b)\,(\lambda_i^2/\alpha_i^2)/S_i(\theta_b)$ and $\partial_{i^b}G_i(\theta_b)=G_i(\theta_b)\,(\lambda_{i^b}^2/\alpha_{i^b}^2)/S_i(\theta_b)$ are the partial derivatives of $G_i(\theta_b)$ in $\alpha_i(\theta_b)$ and $\alpha_{i^b}(\theta_b)$, with $S_i(\theta_b)=\lambda_i^2/\alpha_i+\lambda_{i^b}^2/\alpha_{i^b}$. These are the KKT conditions of the Lagrangian (EC.16) of the epigraph program (EC.14).
--
--   For $k\ge3$, $B_\Xi$ contains every parameter and this is the printed system.
--
--   Differences from the source:
--   - correction: (EC.20) "$\forall b$" → (EC.20) for $\theta_b\in B_\Xi$, with $\alpha_{i^b}(\theta_b)=0$ assumed for $\theta_b\notin B_\Xi$; reason: the printed system has no solution when $k=2$: with $B=2$, $p=(0.6,0.4)$, $\lambda\equiv1$, $y_\cdot(\theta_1)=(0,1)$, $y_\cdot(\theta_2)=(1,0)$, (EC.20) at $\theta_2$ has an empty sum and forces $\gamma=0$, then (EC.19) at $(2,\theta_1)$ forces $\rho=0$ (since $\partial G>0$), contradicting (EC.18), although (20) has an optimum (continuous objective on a compact simplex).
--   - reading: the hypotheses on $\boldsymbol\alpha$ (zero ratio, positivity) → hypotheses of the iff; reason: the page derives the KKT system after proving that optimal allocations have these properties, and its Lagrangian (EC.16) sums $\alpha$ only over $(\Xi^{\mathrm{adv}})^c$ "thanks to the last optimality condition".
--   - reading: KKT conditions → (EC.17)–(EC.21) together with primal feasibility $C\le W_i(\theta_b)G_i(\theta_b)$ on $\Xi$; reason: KKT conditions are stated at a feasible point $(C,\boldsymbol\alpha)$ of (EC.14).
--   - reading: the partial derivatives in (EC.19)–(EC.20) → their closed forms $\partial_iG_i$, $\partial_{i^b}G_i$; reason: these are the derivatives at allocations with the positivity of hypothesis 2 (milestone on partial derivatives).
--   - reading: standing hypotheses $k\ge2$, $p_b>0$, $\lambda_i(\theta_b)>0$ (standard deviation) → fields of the problem; reason: for $k=1$ the objective is a minimum over the empty set, $\Theta$ is the support of $\pi$, and every formula divides by $p_b$ and $\lambda^2$.
--   - encoding: solutions, parameters and $\alpha$ → `Fin k`, `Fin B`, `Fin k → Fin B → ℝ`, with $i^b$, $i^*$ as fields characterized by their defining properties, and the minimum as `Finset.inf'`; reason: Lean convention; same instances.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, proof of Theorem 3, p.ec9, (EC.16)–(EC.21)

import Mathlib
import Definitions.Def_MPBSelect_Problem
import Definitions.Def_MPBSelect_feasibleSet
import Definitions.Def_MPBSelect_Problem_Xi
import Definitions.Def_MPBSelect_Problem_W
import Definitions.Def_MPBSelect_Problem_G
import Definitions.Def_MPBSelect_Problem_Bx
import Definitions.Def_MPBSelect_Problem_IsOptimal
import Definitions.Def_MPBSelect_Problem_ZeroRatio
import Definitions.Def_MPBSelect_Problem_dGdOwn

namespace MPBSelect

open Finset

/-- **KKT conditions (EC.17)–(EC.21) are necessary and sufficient (corrected).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, proof of Theorem 3,
p.ec9, (EC.16)–(EC.21): "Further, the uniform allocation, αi(θb) = 1/kB, with C = 0 becomes an
interior point, which is strictly feasible. Hence, Slater's condition implies that the strong
duality holds; thus, Karush-Kuhn-Tucker (KKT) conditions become necessary and sufficient
conditions for optimality."

Let `α` be feasible for (20), with the properties the proof has established for optimal
allocations at that point: the zero sampling ratio, `α_{i^b}(θ_b) = 0` for `θ_b ∉ Bx`,
`α_i(θ_b) > 0` on `Ξ` and `α_{i^b}(θ_b) > 0` for `θ_b ∈ Bx`. Then `α` is optimal for (20) iff
there are `C`, `γ` and `ρ = {ρ_i(θ_b)}` with
* `C ≤ W_i(θ_b) G_i(θ_b)` on `Ξ` (`(C, α)` is feasible for (EC.14));
* (EC.17) `ρ_i(θ_b) ≥ 0` on `Ξ`;
* (EC.18) `−1 + Σ_{(i,θ_b) ∈ Ξ} ρ_i(θ_b) = 0`;
* (EC.19) `−ρ_i(θ_b) W_i(θ_b) ∂G_i(θ_b)/∂α_i(θ_b) + γ = 0` on `Ξ`;
* (EC.20) `−Σ_{i ≠ i^b, i*} ρ_i(θ_b) W_i(θ_b) ∂G_i(θ_b)/∂α_{i^b}(θ_b) + γ = 0` for every `θ_b ∈ Bx`;
* (EC.21) `ρ_i(θ_b)(C − W_i(θ_b) G_i(θ_b)) = 0` on `Ξ`.

The partial derivatives are the explicit expressions `Problem.dGdOwn` and `Problem.dGdOpt`
(see `theorem_3_partial_derivatives`).

**Formalization Note** (corrected) The page requires (EC.20) for every `b`. When `k = 2` and
`θ_b ∉ Θ_{i*}`, its sum is empty and it forces `γ = 0`; (EC.19) then forces `ρ = 0`,
contradicting (EC.18), so the printed system has no solution although an optimum exists
(instance: `p = (0.6, 0.4)`, `λ ≡ 1`, `y(θ_1) = (0, 1)`, `y(θ_2) = (1, 0)`). (EC.20) is therefore
required on `Bx` only; for `k ≥ 3`, `Bx` is every parameter and the system is the printed one. -/
theorem theorem_3_kkt {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ)
    (hα : α ∈ feasibleSet k B) (hzero : P.ZeroRatio α)
    (hout : ∀ b ∉ P.Bx, α (P.ib b) b = 0)
    (hpos : ∀ x ∈ P.Xi, 0 < α x.1 x.2) (hposib : ∀ b ∈ P.Bx, 0 < α (P.ib b) b) :
    P.IsOptimal α ↔
      ∃ (C γ : ℝ) (ρ : Fin k → Fin B → ℝ),
        (∀ x ∈ P.Xi, C ≤ P.W x.1 x.2 * P.G α x.1 x.2) ∧
        (∀ x ∈ P.Xi, 0 ≤ ρ x.1 x.2) ∧
        -1 + ∑ x ∈ P.Xi, ρ x.1 x.2 = 0 ∧
        (∀ x ∈ P.Xi, -ρ x.1 x.2 * P.W x.1 x.2 * P.dGdOwn α x.1 x.2 + γ = 0) ∧
        (∀ b ∈ P.Bx,
          -(∑ i ∈ univ.filter (fun i : Fin k => i ≠ P.ib b ∧ i ≠ P.istar),
              ρ i b * P.W i b * P.dGdOpt α i b) + γ = 0) ∧
        (∀ x ∈ P.Xi, ρ x.1 x.2 * (C - P.W x.1 x.2 * P.G α x.1 x.2) = 0) := by sorry

end MPBSelect
