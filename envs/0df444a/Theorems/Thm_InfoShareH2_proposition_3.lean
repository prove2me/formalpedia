-- Prove2me | Theorems.Thm_InfoShareH2_proposition_3
-- name    : InfoShareH2.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:44.977688+00:00
-- url     : https://prove2.me/theorems/8544d51a-db12-46d4-8984-84c8c08215d4
-- title:
--   Proposition 3 — the $\varepsilon$-optimal family $\tilde\psi_\delta=\frac{1+z}2\exp\bigl(\gamma_\sigma\frac{z-1}{1+\delta+z}\bigr)$
-- statement:
--   Let $\sigma_\epsilon>0$ and $0<\sigma\le\sigma_\epsilon/2$, and let $\gamma_\sigma=-\log(2\sigma/\sigma_\epsilon)$. For $\delta>0$ consider
--
--   $$\tilde\psi_\delta(z)=\frac{1+z}{2}\exp\Bigl(\gamma_\sigma\frac{z-1}{1+\delta+z}\Bigr),$$
--
--   holomorphic on $|z|<1+\delta$, with Taylor coefficients $(\tilde\psi_{\delta,n})_{n\ge0}$. Then:
--
--   1. for every $\delta>0$ the coefficients are real, $\tilde\psi_\delta\in\tilde\Psi$, and $\tilde\psi_\delta$ satisfies Assumption 2;
--   2. $\sigma^2_{S|NS}(\tilde\psi_\delta)\to\sigma^2$ as $\delta\to0^+$;
--   3. $\sigma^2_I(\tilde\psi_\delta)\to\Sigma^2_{NS}(\sigma)$ as $\delta\to0^+$, where $\Sigma^2_{NS}(\sigma)$ is the infimum (26).
--
--   The family approaches the no-sharing frontier although no policy attains it; each $\tilde\psi_\delta$ itself has $\sigma^2_{S|NS}(\tilde\psi_\delta)>\sigma^2$.
--
--   Differences from the source:
--   - reading: the limits for "the function ψ̃_δ" → also asserts that each ψ̃_δ (δ > 0) has real Taylor coefficients, lies in Ψ̃ and satisfies Assumption 2; reason: the limits are statements about admissible policies of (26); §9.8 notes ψ̃_δ is holomorphic and nonzero on D_{1+δ}
--   - encoding: the policy ψ̃_δ → real parts of the Taylor coefficients of ψ̃_δ at 0 (which are real); reason: policies are real sequences
--   - encoding: δ → 0+, Σ²_NS(σ) → limits along 𝓝[>] 0; the defined infimum SigmaNSsq; reason: Lean convention
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, Proposition 3, p.21 (restated p.28; proof §9.8, pp.44–45)

import Mathlib
import Definitions.Def_InfoShareH2_Model

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **Proposition 3 (ε-optimal policies).**
SSRN 4319721 (v. 2024-01-20), Proposition 3, p.21 (restated p.28; proof §9.8, pp.44–45). "For
`0 < σ ≤ (1/2)σ_ε`, consider the function `ψ̃_δ(z) = ((1 + z)/2) exp(γ_σ (z − 1)/(1 + δ + z))`, where
`γ_σ = −log(2σ/σ_ε)`. We have `σ²_S|NS(ψ̃_δ) → σ²`, and `σ²_I(ψ̃_δ) → Σ²_NS(σ)` as `δ → 0+`."

`ψ̃_δ`'s coefficients are its Taylor coefficients at `0` (it is holomorphic on `|z| < 1 + δ`).
`Σ²_NS(σ)` is the infimum (26) (`SigmaNSsq`), not its closed form.

**Formalization Note** The limits presuppose that each `ψ̃_δ` (`δ > 0`) is an admissible policy of
(26): real coefficients in `Ψ̃` satisfying Assumption 2 (§9.8: "holomorphic and nonzero in
`D_{1+δ}`"). This is stated as the first conjunct. `ψ̃_δ` is not feasible at level `σ`
(`σ²_S|NS(ψ̃_δ) > σ²`), and no such claim is made. -/
theorem proposition_3 (σε σ : ℝ) (hσε : 0 < σε) (hσ : 0 < σ) (hσ2 : σ ≤ σε / 2) :
    let γσ : ℝ := -Real.log (2 * σ / σε)
    let f : ℝ → ℂ → ℂ := fun δ z => (1 + z) / 2 * exp ((γσ : ℂ) * (z - 1) / (1 + (δ : ℂ) + z))
    let ψδ : ℝ → ℕ → ℝ := fun δ n => (taylorCoeff (f δ) n).re
    (∀ δ > (0 : ℝ), (∀ n, (taylorCoeff (f δ) n).im = 0) ∧ ψδ δ ∈ PsiTilde ∧ Assumption2 (ψδ δ)) ∧
    Tendsto (fun δ => nsVar σε (ψδ δ)) (𝓝[>] (0 : ℝ)) (𝓝 (σ ^ 2)) ∧
    Tendsto (fun δ => invVar σε (ψδ δ)) (𝓝[>] (0 : ℝ)) (𝓝 (SigmaNSsq σε σ)) := by sorry

end InfoShareH2
