-- Prove2me | Theorems.Thm_MPBSelect_theorem_3_zero_ratio
-- name    : MPBSelect.theorem_3_zero_ratio
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:52.636384+00:00
-- url     : https://prove2.me/theorems/35f64edb-e679-4e07-ad79-37bcbaf9243f
-- title:
--   Proof of Theorem 3, pp.ec8–ec9 — every optimal allocation has $\alpha_{i^*}(\theta_b)=0$ on $\Theta^c_{i^*}$
-- statement:
--   Consider an MPB problem (with $k\ge2$, $p_b>0$, $\sum_bp_b=1$, assumptions (i)–(ii) and $\lambda>0$). If $\boldsymbol\alpha$ is optimal for the relaxed OCBA problem (20), then
--   $$
--   \alpha_{i^*}(\theta_b)=0\qquad\text{for all }\theta_b\in\Theta^c_{i^*}.
--   $$
--   The coordinates $\alpha_{i^*}(\theta_b)$, $\theta_b\notin\Theta_{i^*}$, appear in no term of the objective of (20), so budget spent there is wasted. This is the necessity half of the third optimality condition of Theorem 3.
--
--   Differences from the source:
--   - reading: standing hypotheses $k\ge2$, $p_b>0$, $\lambda_i(\theta_b)>0$ (standard deviation) → fields of the problem; reason: for $k=1$ the objective is a minimum over the empty set, $\Theta$ is the support of $\pi$, and every formula divides by $p_b$ and $\lambda^2$.
--   - encoding: solutions, parameters and $\alpha$ → `Fin k`, `Fin B`, `Fin k → Fin B → ℝ`, with $i^b$, $i^*$ as fields characterized by their defining properties, and the minimum as `Finset.inf'`; reason: Lean convention; same instances.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, proof of Theorem 3, pp.ec8–ec9

import Mathlib
import Definitions.Def_MPBSelect_Problem
import Definitions.Def_MPBSelect_Problem_IsOptimal
import Definitions.Def_MPBSelect_Problem_ZeroRatio

namespace MPBSelect

/-- **Every optimal allocation gives the MPB zero ratio at its adversarial parameters.**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, proof of Theorem 3,
pp.ec8–ec9: "On the one hand, Gi(θb) for (i,θb) ∈ Ξadv does not appear in this program. For any
such (i,θb), suppose αi(θb) > 0. Then, we can always strictly improve the objective function
value by setting αi(θb) = 0 and increasing αi′(θb′) at (i′,θb′) pairs for which the first
constraint of (EC.14) is binding. Hence αi∗(θb) = 0 for all θb ∈ Θc_{i∗} at optimality."

If `α` is optimal for (20), then `α_{i*}(θ_b) = 0` for every `θ_b` with `i^b ≠ i*`. -/
theorem theorem_3_zero_ratio {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ)
    (hα : P.IsOptimal α) : P.ZeroRatio α := by sorry

end MPBSelect
