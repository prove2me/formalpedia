-- Prove2me | Theorems.Thm_MPBSelect_theorem_3_partial_derivatives
-- name    : MPBSelect.theorem_3_partial_derivatives
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:28:53.506764+00:00
-- url     : https://prove2.me/theorems/f41c867c-edf3-469f-907e-f1e2702440bb
-- title:
--   Proof of Theorem 3, p.ec10 — partial derivatives of $G_i(\theta_b)$ and their ratio (corrected: denominator $\lambda_i^2/\alpha_i+\lambda_{i^b}^2/\alpha_{i^b}$)
-- statement:
--   Consider an MPB problem (with $k\ge2$, $p_b>0$, $\sum_bp_b=1$, assumptions (i)–(ii) and $\lambda>0$). Let $i\ne i^b$, and let $\boldsymbol\alpha$ have $\alpha_i(\theta_b)>0$ and $\alpha_{i^b}(\theta_b)>0$. Write
--   $$
--   S=\frac{\lambda_i^2(\theta_b)}{\alpha_i(\theta_b)}+\frac{\lambda_{i^b}^2(\theta_b)}{\alpha_{i^b}(\theta_b)} .
--   $$
--   Varying one coordinate of $\boldsymbol\alpha$ with all others fixed,
--
--   1. $\dfrac{\partial G_i(\theta_b)}{\partial\alpha_i(\theta_b)}=G_i(\theta_b)\,\dfrac{\lambda_i^2(\theta_b)/\alpha_i^2(\theta_b)}{S}$;
--   2. $\dfrac{\partial G_i(\theta_b)}{\partial\alpha_{i^b}(\theta_b)}=G_i(\theta_b)\,\dfrac{\lambda_{i^b}^2(\theta_b)/\alpha_{i^b}^2(\theta_b)}{S}$;
--   3. their ratio, used in the third equality of (EC.22), is
--   $$
--   \frac{\partial G_i(\theta_b)/\partial\alpha_{i^b}(\theta_b)}{\partial G_i(\theta_b)/\partial\alpha_i(\theta_b)}=\frac{\lambda_{i^b}^2(\theta_b)/\alpha_{i^b}^2(\theta_b)}{\lambda_i^2(\theta_b)/\alpha_i^2(\theta_b)} .
--   $$
--
--   The ratio identity is what turns the KKT conditions (EC.19)–(EC.20) into the global balance condition of Theorem 3.
--
--   Differences from the source:
--   - correction: denominator $\lambda_i^2/\alpha_i^2+\lambda_{i^b}^2/\alpha_{i^b}^2$ → $\lambda_i^2/\alpha_i+\lambda_{i^b}^2/\alpha_{i^b}$; reason: the printed identity is false: with $\lambda\equiv1$, $y_i-y_{i^b}=1$, $\alpha_i=\alpha_{i^b}=1/2$, one has $G_i=1/8$, the true partial derivative is $1/8$, and the printed right side is $1/16$. The ratio in clause 3 is the same under both forms.
--   - reading: the identity below (EC.22), stated without quantifier inside the sum over $i\ne i^b,i^*$ → stated for every $i\ne i^b$ with both ratios positive, together with the derivative in $\alpha_{i^b}(\theta_b)$ and the ratio used in the third equality of (EC.22); reason: $G_i(\theta_b)$ is defined for $i\ne i^b$, and (EC.22) uses exactly these two derivatives and their ratio.
--   - reading: standing hypotheses $k\ge2$, $p_b>0$, $\lambda_i(\theta_b)>0$ (standard deviation) → fields of the problem; reason: for $k=1$ the objective is a minimum over the empty set, $\Theta$ is the support of $\pi$, and every formula divides by $p_b$ and $\lambda^2$.
--   - encoding: a partial derivative in the coordinate $\alpha_j(\theta_b)$ → `HasDerivAt` of $t\mapsto G$ at the allocation updated at $(j,\theta_b)$ to $t$ (`Function.update`); solutions, parameters and $\alpha$ → `Fin k`, `Fin B`, `Fin k → Fin B → ℝ`; reason: Lean convention; same instances.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, proof of Theorem 3, (EC.22) and the line below it, p.ec10

import Mathlib
import Definitions.Def_MPBSelect_Problem
import Definitions.Def_MPBSelect_Problem_G
import Definitions.Def_MPBSelect_Problem_dGdOwn

namespace MPBSelect

/-- **Partial derivatives of the pairwise rate (corrected).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, proof of Theorem 3,
(EC.22) and the line below it, p.ec10: "For the third equality, we exploit that
∂Gi(θb)/∂αi(θb) = Gi(θb) (λ²i(θb)/α²i(θb)) / (λ²i(θb)/α²i(θb) + λ²_{i^b}(θb)/α²_{i^b}(θb))."

Let `i ≠ i^b`, `α_i(θ_b) > 0` and `α_{i^b}(θ_b) > 0`, and write
`S = λ_i(θ_b)²/α_i(θ_b) + λ_{i^b}(θ_b)²/α_{i^b}(θ_b)`. Then, varying one coordinate of `α` with all
others fixed,
1. `∂G_i(θ_b)/∂α_i(θ_b) = G_i(θ_b) (λ_i(θ_b)²/α_i(θ_b)²) / S`;
2. `∂G_i(θ_b)/∂α_{i^b}(θ_b) = G_i(θ_b) (λ_{i^b}(θ_b)²/α_{i^b}(θ_b)²) / S`;
3. their ratio, used in the third equality of (EC.22), is
   `(∂G_i/∂α_{i^b}) / (∂G_i/∂α_i) = (λ_{i^b}(θ_b)²/α_{i^b}(θ_b)²) / (λ_i(θ_b)²/α_i(θ_b)²)`.

**Formalization Note** (corrected) The page's denominator `λ²_i/α²_i + λ²_{i^b}/α²_{i^b}` is
wrong: with `λ ≡ 1`, `y_i − y_{i^b} = 1`, `α_i = α_{i^b} = 1/2`, one has `G = 1/8` and the true
partial derivative is `1/8`, while the printed right side is `1/16`. The correct denominator is
`S`. The ratio in clause 3 is the same under both forms. A coordinate update of `α` at
`(j, θ_b)` is `Function.update α j (Function.update (α j) b t)`. -/
theorem theorem_3_partial_derivatives {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ)
    (i : Fin k) (b : Fin B) (hi : i ≠ P.ib b) (hαi : 0 < α i b) (hαib : 0 < α (P.ib b) b) :
    HasDerivAt (fun t : ℝ => P.G (Function.update α i (Function.update (α i) b t)) i b)
        (P.dGdOwn α i b) (α i b) ∧
    HasDerivAt
        (fun t : ℝ => P.G (Function.update α (P.ib b) (Function.update (α (P.ib b)) b t)) i b)
        (P.dGdOpt α i b) (α (P.ib b) b) ∧
    P.dGdOpt α i b / P.dGdOwn α i b =
      (P.lam (P.ib b) b ^ 2 / α (P.ib b) b ^ 2) / (P.lam i b ^ 2 / α i b ^ 2) := by sorry

end MPBSelect
