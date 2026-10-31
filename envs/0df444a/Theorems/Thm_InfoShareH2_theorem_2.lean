-- Prove2me | Theorems.Thm_InfoShareH2_theorem_2
-- name    : InfoShareH2.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:40.274984+00:00
-- url     : https://prove2.me/theorems/dba9648a-9db3-4df3-8abd-1d22402b9dea
-- title:
--   Theorem 2 — no-sharing frontier: $\Sigma^2_{NS}(\sigma)=\frac{\sigma_\epsilon^2}4(5-\log\frac{4\sigma^2}{\sigma_\epsilon^2})$ below $\sigma_\epsilon/2$, the full-sharing value above
-- statement:
--   Let $\sigma_\epsilon>0$ be the standard deviation of the demand shocks. Without information sharing the supplier's one-step forecast error for an order policy $\tilde\psi$ is Kolmogorov's expression
--
--   $$\sigma^2_{S|NS}(\tilde\psi)=\sigma_\epsilon^2\exp\Bigl(\frac1{2\pi}\int_{-\pi}^{\pi}\log\bigl(\tilde\psi(e^{-i\lambda})\tilde\psi(e^{i\lambda})\bigr)\,d\lambda\Bigr),$$
--
--   and the efficient frontier (26) is
--
--   $$\Sigma^2_{NS}(\sigma)=\inf\Bigl\{\sigma_I^2(\tilde\psi)=\sigma_\epsilon^2\Bigl(1+\sum_{k\ge1}\Bigl(\sum_{n<k}\tilde\psi_n-1\Bigr)^2\Bigr):\ \tilde\psi\in\tilde\Psi\text{ satisfies Assumption 2},\ \sigma^2_{S|NS}(\tilde\psi)\le\sigma^2\Bigr\}.$$
--
--   Then for every $\sigma>0$
--
--   $$\Sigma^2_{NS}(\sigma)=\begin{cases}\dfrac{\sigma_\epsilon^2}{4}\Bigl(5-\log\dfrac{4\sigma^2}{\sigma_\epsilon^2}\Bigr), & 0<\sigma<\tfrac12\sigma_\epsilon,\\[2mm] \sigma_\epsilon^2+\bigl((\sigma_\epsilon-\sigma)^+\bigr)^2, & \sigma\ge\tfrac12\sigma_\epsilon.\end{cases}$$
--
--   For $\sigma\ge\sigma_\epsilon/2$ the frontier coincides with the full-sharing frontier of Theorem 1, so sharing demand information has no value there; for $\sigma<\sigma_\epsilon/2$ it is strictly larger, and the ratio to the full-sharing frontier tends to infinity as $\sigma\downarrow0$. The infimum is not attained for $\sigma<\sigma_\epsilon/2$.
--
--   Differences from the source:
--   - reading: "Under Assumptions 1 and 2" → the infimum (26) ranges over ψ̃ ∈ Ψ̃ that satisfy Assumption 2; reason: p.28: "we solve the optimization problem (26) … with respect to all functions in H² that satisfy Assumption 2"; Assumption 1 enters through Ψ̃ and σ_ε > 0
--   - reading: "if the retailer does not share any information, i.e. F^S(t) = M_O(t)" → Σ²_NS is the explicit problem (26) with the Kolmogorov expression for σ²_S|NS; reason: (26) is the paper’s definition of Σ²_NS; the stochastic model only motivates it
--   - encoding: real MA coefficients with "∑ψ̃_n = 1" and boundary values ψ̃(e^{−iλ}) → ψ : ℕ → ℝ, convergence of partial sums (not HasSum), radial limits via limUnder; reason: the orders are real (Assumption 1(b), §9.3); ψ̃ ∈ ℓ² need not be absolutely summable; p.22 defines boundary values as radial limits
--   - encoding: ψ̃(e^{−iλ})ψ̃(e^{iλ}); θ_n; inf; (x)⁺ → |ψ̃(e^{−iλ})|²; Θ^{(n)}(0)/n!; real sInf of attained values; max x 0; reason: real coefficients make the product a squared modulus; Real.log 0 = 0 never fires on Ψ̃ since log|ψ̃| is integrable for ψ̃ ≠ 0
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, Theorem 2, p.20 (restated p.29; proof §9.7, pp.40–44); (26) p.20, Assumption 2 p.27

import Mathlib
import Definitions.Def_InfoShareH2_Model

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **Theorem 2 (no information sharing frontier).**
Caldentey–Giloni–Hurvich–Zhang, SSRN 4319721 (v. 2024-01-20), Theorem 2, p.20 (restated p.29;
proof §9.7, pp.40–44). "Under Assumptions 1 and 2, if the retailer does not share any information
with the supplier, i.e. `F^S(t) = M_O(t)`, then
`Σ²_NS(σ) = (σ_ε²/4)(5 − log(4σ²/σ_ε²))` when `0 < σ < σ_ε/2`, and
`Σ²_NS(σ) = σ_ε² + ((σ_ε − σ)⁺)²` when `σ ≥ σ_ε/2`."

`SigmaNSsq σε σ` is the infimum (26) of `σ²_I(ψ̃)` over `ψ̃ ∈ Ψ̃` satisfying Assumption 2 with
`σ²_S|NS(ψ̃) ≤ σ²`.

**Formalization Note** `(x)⁺` is `max x 0`. The infimum is a real `sInf`; it is not attained for
`σ < σ_ε/2`. -/
theorem theorem_2 (σε σ : ℝ) (hσε : 0 < σε) (hσ : 0 < σ) :
    (σ < σε / 2 → SigmaNSsq σε σ = σε ^ 2 / 4 * (5 - Real.log (4 * σ ^ 2 / σε ^ 2))) ∧
    (σε / 2 ≤ σ → SigmaNSsq σε σ = σε ^ 2 + (max (σε - σ) 0) ^ 2) := by sorry

end InfoShareH2
