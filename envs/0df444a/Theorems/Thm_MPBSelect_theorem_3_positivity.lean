-- Prove2me | Theorems.Thm_MPBSelect_theorem_3_positivity
-- name    : MPBSelect.theorem_3_positivity
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:51.505872+00:00
-- url     : https://prove2.me/theorems/a4c77884-6953-40d3-a2bf-387dacec9b1c
-- title:
--   Proof of Theorem 3, p.ec9 — optimal value positive, optimal $\alpha$ positive where (20) needs it (corrected: positivity only where $\Xi$ has a pair at $\theta_b$)
-- statement:
--   Consider an MPB problem (with $k\ge2$, $p_b>0$, $\sum_bp_b=1$, assumptions (i)–(ii) and $\lambda>0$), and let $B_\Xi$ be the set of parameters $\theta_b$ at which $\Xi$ has a pair. Then:
--
--   1. the uniform allocation $\alpha_i(\theta_b)=1/(kB)$ is feasible for (20) and
--   $$
--   \min_{(i,\theta_b)\in\Xi}W_i(\theta_b)G_i(\theta_b)>0\quad\text{at }\alpha\equiv 1/(kB);
--   $$
--   2. every optimal $\boldsymbol\alpha$ for (20) has positive objective value, and
--      - $\alpha_i(\theta_b)>0$ for all $(i,\theta_b)\in\Xi$,
--      - $\alpha_{i^b}(\theta_b)>0$ for all $\theta_b\in B_\Xi$,
--      - $\alpha_{i^b}(\theta_b)=0$ for all $\theta_b\notin B_\Xi$.
--
--   For $k\ge3$, $B_\Xi$ contains every parameter and clause 2 says that optimal ratios are positive on $(\Xi^{\mathrm{adv}})^c=\Xi\cup\{(i^b,\theta_b)\}$, which is the paper's claim. The last bullet is vacuous for $k\ge3$.
--
--   Differences from the source:
--   - correction: "optimal $\alpha_i(\theta_b)$ must be positive for all $(i,\theta_b)\in(\Xi^{\mathrm{adv}})^c$" → positive on $\Xi$ and at $(i^b,\theta_b)$ for $\theta_b\in B_\Xi$, and $\alpha_{i^b}(\theta_b)=0$ for $\theta_b\notin B_\Xi$; reason: the printed claim is false for $k=2$: with $B=2$, $p=(0.6,0.4)$, $\lambda\equiv1$, $y_\cdot(\theta_1)=(0,1)$, $y_\cdot(\theta_2)=(1,0)$ one has $i^*=1$, $\Xi=\{(2,\theta_1)\}$, $\Xi^{\mathrm{adv}}=\{(1,\theta_2)\}$; the pair $(2,\theta_2)$ lies in $(\Xi^{\mathrm{adv}})^c$, but $\alpha_2(\theta_2)$ enters no term of the objective, so every optimal $\boldsymbol\alpha$ has $\alpha_2(\theta_2)=0$ (moving that mass to $\theta_1$ strictly raises $W_2(\theta_1)G_2(\theta_1)$).
--   - reading: standing hypotheses $k\ge2$, $p_b>0$, $\lambda_i(\theta_b)>0$ (standard deviation) → fields of the problem; reason: for $k=1$ the objective is a minimum over the empty set, $\Theta$ is the support of $\pi$, and every formula divides by $p_b$ and $\lambda^2$.
--   - encoding: solutions, parameters and $\alpha$ → `Fin k`, `Fin B`, `Fin k → Fin B → ℝ`, with $i^b$, $i^*$ as fields characterized by their defining properties, and the minimum as `Finset.inf'`; reason: Lean convention; same instances.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, proof of Theorem 3, p.ec9

import Mathlib
import Definitions.Def_MPBSelect_Problem
import Definitions.Def_MPBSelect_feasibleSet
import Definitions.Def_MPBSelect_Problem_Xi
import Definitions.Def_MPBSelect_Problem_Bx
import Definitions.Def_MPBSelect_Problem_ldr
import Definitions.Def_MPBSelect_Problem_IsOptimal

namespace MPBSelect

open Finset

/-- **Positive optimal value and positivity of optimal allocations (corrected).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, proof of Theorem 3,
p.ec9: "Suppose αi(θb) = 0 for some (i,θb) ∈ (Ξadv)c. Then, Gi(θb) = 0 or Gj(θb) = 0 for some j
(when i = i^b). This implies C ≤ 0. However, if we set αi(θb) = 1/kB for all 1 ≤ i ≤ k,
1 ≤ b ≤ B, the optimal C must be positive; for all (i,θb) ∈ Ξ, Wi(θb) > 0 and positive αi(θb)'s
make Gi(θb) positive. Therefore, optimal αi(θb) must be positive for all (i,θb) ∈ (Ξadv)c."

1. The uniform allocation `α_i(θ_b) = 1/(kB)` is feasible and has positive objective value.
2. Every optimal `α` has `LDR(α) > 0`, `α_i(θ_b) > 0` on `Ξ`, `α_{i^b}(θ_b) > 0` for every
   `θ_b ∈ Bx` (the parameters carrying a pair of `Ξ`), and `α_{i^b}(θ_b) = 0` for `θ_b ∉ Bx`.

**Formalization Note** (corrected) The page claims positivity on all of `(Ξ^adv)^c`, which is
`Ξ ∪ {(i^b, θ_b)}`. That is false when `k = 2`: with `p = (0.6, 0.4)`, `λ ≡ 1`,
`y(θ_1) = (0, 1)`, `y(θ_2) = (1, 0)`, the coordinate `α_2(θ_2)` enters no term of (20), and every
optimal `α` has `α_2(θ_2) = 0`. For `k ≥ 3`, `Bx` is every parameter and clause 2 is the
printed claim. -/
theorem theorem_3_positivity {k B : ℕ} (P : Problem k B) :
    ((fun _ _ => 1 / ((k : ℝ) * B)) ∈ feasibleSet k B ∧
      0 < P.ldr (fun _ _ => 1 / ((k : ℝ) * B))) ∧
    ∀ α : Fin k → Fin B → ℝ, P.IsOptimal α →
      0 < P.ldr α ∧
      (∀ x ∈ P.Xi, 0 < α x.1 x.2) ∧
      (∀ b ∈ P.Bx, 0 < α (P.ib b) b) ∧
      (∀ b ∉ P.Bx, α (P.ib b) b = 0) := by sorry

end MPBSelect
