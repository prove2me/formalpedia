-- Prove2me | Theorems.Thm_GMMPostSamp_Main_lemma_10
-- name    : GMMPostSamp.Main.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:25:47.992936+00:00
-- url     : https://prove2.me/theorems/b7ed56a9-c4dc-404a-987f-b934f77b5c24
-- title:
--   Lemma 10 — under the prior, min weight ≥ τ and (3/4)I ⪯ AᵀA ⪯ (5/4)I with probability ≥ 1 − δ/2
-- statement:
--   There is a universal constant $C>0$ such that for all $k,d,n\ge1$, $\sigma>0$, $0<a\le A$, $\alpha\in[a,A]^k$ and $\delta\in(0,\tfrac12)$ with $d\ge C(k+\log\frac1\delta)$, setting $\tau=\frac1{Ak}(\frac{\delta}{8k})^{1/a}$,
--   $$\Pr_{\text{Model 1}}\big[\theta^\star\in R(\tau)\big]\ge1-\frac\delta2,$$
--   where $R(\tau)=\{\theta\in\Theta:\min_iw_i\ge\tau,\ \tfrac34I_k\preceq A^\top A\preceq\tfrac54I_k\}$ with $A=[\mu_1|\cdots|\mu_k]$ (52). It supplies the regularity under which the moment estimator of Proposition 4 works.
--
--   **Formalization Note.** $\frac34I_k\preceq A^\top A\preceq\frac54I_k$ is written as $\frac34\|u\|^2\le\|\sum_iu_i\mu_i\|^2\le\frac54\|u\|^2$ for all $u\in\mathbb R^k$.
--
--   Differences from the source:
--   - reading: (k, d, n) ∈ N³ and 'for a universal constant C > 0' → k, d, n ≥ 1 and ∃ C > 0 quantified before all parameters; reason: N is read as the positive integers; C is universal
--   - encoding: (3/4)I_k ⪯ AᵀA ⪯ (5/4)I_k → (3/4)‖u‖² ≤ ‖Σ u_i µ_i‖² ≤ (5/4)‖u‖² for all u; reason: uᵀAᵀAu = ‖Au‖²
--   - encoding: P[θ⋆ ∈ R(τ)] ≥ 1 − δ/2 under Model 1 → joint {p | p.1 ∈ R(τ)} ≥ ofReal(1 − δ/2); reason: θ⋆ is the first coordinate of the Model-1 joint law
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 42, Lemma 10

import Mathlib
import Definitions.Def_PolyVoting_dirichletMeasure
import Definitions.Def_GMMPostSamp_Main_Toolkit
import Definitions.Def_GMMPostSamp_Main_Model

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Lemma 10 (p. 42): there is a universal `C > 0` such that for `δ ∈ (0, 1/2)` and
`d ≥ C(k + log(1/δ))`, with `τ = (1/(Ak))(δ/(8k))^{1/a}`, the Model-1 parameter `θ⋆` lies in the
regularity set `R(τ)` (52) with probability at least `1 − δ/2`. -/
theorem lemma_10 : ∃ C : ℝ, 0 < C ∧
    ∀ k d n : ℕ, 1 ≤ k → 1 ≤ d → 1 ≤ n → ∀ (σ a A δ : ℝ) (α : Fin k → ℝ),
      0 < σ → 0 < a → a ≤ A → (∀ i, α i ∈ Set.Icc a A) → 0 < δ → δ < 1 / 2 →
      C * ((k : ℝ) + Real.log (1 / δ)) ≤ d →
      ENNReal.ofReal (1 - δ / 2) ≤
        joint k d n σ α {p | p.1 ∈ Regular ((1 / (A * k)) * (δ / (8 * k)) ^ (1 / a))} := by sorry

end GMMPostSamp.Main
