-- Prove2me | Theorems.Thm_MPBSelect_theorem_3
-- name    : MPBSelect.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:41.163152+00:00
-- url     : https://prove2.me/theorems/c9e2aa7b-a04c-4b44-978d-a66d6ff2c38d
-- title:
--   Theorem 3 — $\boldsymbol\alpha$ is optimal for (20) iff global balance, pairwise balance and zero sampling ratio hold
-- statement:
--   Consider $k\ge2$ solutions and parameters $\theta_1,\dots,\theta_B$ with probabilities $p_b>0$, $\sum_bp_b=1$; conditional means $y_i(\theta_b)$ that are pairwise distinct at each $\theta_b$ (assumption (i)), with conditional optima $i^b=\arg\min_iy_i(\theta_b)$; a unique most probable best $i^*=\arg\max_i\sum_bp_b\mathbf 1\{i=i^b\}$ (assumption (ii)); and standard deviations $\lambda_i(\theta_b)>0$. Let $\Xi=\{(i,\theta_b):i\ne i^*,i\ne i^b\}$, $W_i(\theta_b)$ the balance weights (17) and $G_i(\theta_b)$ the pairwise rates. Consider the relaxed OCBA problem
--   $$
--   \max_{\boldsymbol\alpha}\ \min_{(i,\theta_b)\in\Xi}W_i(\theta_b)G_i(\theta_b)\quad\text{s.t.}\quad\sum_{i=1}^k\sum_{b=1}^B\alpha_i(\theta_b)=1,\ \alpha_i(\theta_b)\ge0. \tag{20}
--   $$
--   Then a feasible $\boldsymbol\alpha$ is optimal for (20) if and only if it satisfies all three of the following.
--
--   1. **Global balance.** For all $1\le b\le B$,
--   $$
--   \frac{\alpha_{i^b}^2(\theta_b)}{\lambda_{i^b}^2(\theta_b)}=\sum_{i\ne i^b,\,i^*}\frac{\alpha_i^2(\theta_b)}{\lambda_i^2(\theta_b)} .
--   $$
--   2. **Pairwise balance.** For all $(i,\theta_b),(j,\theta_{b'})\in\Xi$,
--   $$
--   W_i(\theta_b)G_i(\theta_b)=W_j(\theta_{b'})G_j(\theta_{b'}). \tag{21}
--   $$
--   3. **Zero asymptotic sampling ratio.** $\alpha_{i^*}(\theta_b)=0$ for all $\theta_b\in\Theta^c_{i^*}$.
--
--   The conditions characterize the asymptotically optimal static budget allocation for selecting the most probable best under the relaxed rate (20); the paper's sequential sampling algorithms are designed so that their sampling ratios converge to a solution of this system. The third condition contrasts with classical ranking and selection, where every optimal sampling ratio is positive.
--
--   Differences from the source:
--   - reading: "Any α" → every $\boldsymbol\alpha$ in the feasible set of (20); reason: optimality presupposes feasibility, and the three conditions are invariant under scaling, so for infeasible $\boldsymbol\alpha$ the "if" direction would fail.
--   - reading: standing hypotheses $k\ge2$, $p_b>0$, $\lambda_i(\theta_b)>0$ (standard deviation) → fields of the problem; reason: for $k=1$, $\Xi$ is empty and (20) has no objective; $\Theta$ is the support of $\pi$ and (17) divides by $p_b$; Model (4) has variance $\lambda^2$ and the formulas divide by it.
--   - encoding: solutions, parameters and $\alpha$ → `Fin k`, `Fin B`, `Fin k → Fin B → ℝ`, with $i^b$, $i^*$ as fields characterized by their defining properties, and the minimum over $\Xi$ as `Finset.inf'`; reason: Lean convention; same instances.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Theorem 3, p.17

import Mathlib
import Definitions.Def_MPBSelect_Problem
import Definitions.Def_MPBSelect_feasibleSet
import Definitions.Def_MPBSelect_Problem_IsOptimal
import Definitions.Def_MPBSelect_Problem_GlobalBalance
import Definitions.Def_MPBSelect_Problem_PairwiseBalance
import Definitions.Def_MPBSelect_Problem_ZeroRatio

namespace MPBSelect

/-- **Theorem 3 (Optimality conditions for (20)).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, Theorem 3, p.17:
"Any α is optimal for (20), if and only if, α satisfies the following system of equations:
• (Global balance condition) For all 1 ≤ b ≤ B, α²_{i^b}(θb)/λ²_{i^b}(θb) =
Σ_{i≠i^b,i∗} α²_i(θb)/λ²_i(θb).
• (Pairwise balance condition) For all (i,θb),(j,θb′) ∈ Ξ, {Wi(θb)} given in (17) satisfies
Wi(θb)Gi(θb) = Wj(θb′)Gj(θb′). (21)
• (Zero asymptotic sampling ratio) αi∗(θb) = 0 for all θb ∈ Θc_{i∗}."

For every MPB problem `P` (`k ≥ 2` solutions, `B` parameters with positive probabilities,
assumptions (i)–(ii) of p.7, positive standard deviations) and every allocation `α` in the
feasible set of (20): `α` is optimal for (20) iff it satisfies global balance at every
`θ_b`, pairwise balance (21) at every two pairs of `Ξ`, and the zero sampling ratio at every
`θ_b ∈ Θ^c_{i*}`.

**Formalization Note** `α` ranges over the simplex `Σ_i Σ_b α_i(θ_b) = 1, α ≥ 0` of (20):
optimality presupposes feasibility, and the three conditions are invariant under scaling. -/
theorem theorem_3 {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ)
    (hα : α ∈ feasibleSet k B) :
    P.IsOptimal α ↔ P.GlobalBalance α ∧ P.PairwiseBalance α ∧ P.ZeroRatio α := by sorry

end MPBSelect
