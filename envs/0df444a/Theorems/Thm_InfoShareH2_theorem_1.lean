-- Prove2me | Theorems.Thm_InfoShareH2_theorem_1
-- name    : InfoShareH2.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:52.377806+00:00
-- url     : https://prove2.me/theorems/544c97ae-ca74-410e-9db4-a4c2d10dcc56
-- title:
--   Theorem 1 — full-sharing frontier $\Sigma^2_{FI}(\sigma)=\sigma_\epsilon^2+((\sigma_\epsilon-\sigma)^+)^2$ with a unique MA(1) minimizer
-- statement:
--   Let $\sigma_\epsilon>0$ and $\sigma\ge0$. Under full information sharing the supplier's forecast error is $\sigma^2_{S|FI}(\tilde\psi)=\sigma_\epsilon^2\tilde\psi_0^2$, and the efficient frontier (25) is
--
--   $$\Sigma^2_{FI}(\sigma)=\inf\{\sigma_I^2(\tilde\psi):\tilde\psi\in\tilde\Psi,\ \sigma_\epsilon^2\tilde\psi_0^2\le\sigma^2\}.$$
--
--   Then
--
--   $$\Sigma^2_{FI}(\sigma)=\sigma_\epsilon^2+\bigl((\sigma_\epsilon-\sigma)^+\bigr)^2,$$
--
--   and the infimum is attained by the policy $\tilde\psi^\star$ with $\tilde\psi^\star_0=\min\{1,\sigma/\sigma_\epsilon\}$, $\tilde\psi^\star_1=1-\tilde\psi^\star_0$ and $\tilde\psi^\star_n=0$ for $n\ge2$, an MA(1) order. More precisely:
--
--   1. $\tilde\psi^\star\in\tilde\Psi$ and $\sigma_\epsilon^2(\tilde\psi^\star_0)^2\le\sigma^2$;
--   2. $\sigma_I^2(\tilde\psi^\star)=\Sigma^2_{FI}(\sigma)$;
--   3. every feasible $\tilde\psi$ with $\sigma_I^2(\tilde\psi)=\Sigma^2_{FI}(\sigma)$ equals $\tilde\psi^\star$.
--
--   The theorem gives the full-sharing benchmark, and the no-sharing frontier of Theorem 2 coincides with it for $\sigma\ge\sigma_\epsilon/2$.
--
--   Differences from the source:
--   - reading: σ unrestricted → σ ≥ 0; reason: σ bounds a standard deviation; for σ < 0 the formula fails (σ_ε = 1, σ = −1: Σ²_FI = 1, formula gives 5)
--   - reading: "the optimal solution … is given by" → ψ⋆ is feasible, attains Σ²_FI(σ), and is the only feasible policy that does; reason: §9.6 concludes "the unique optimal solution"
--   - reading: "Under Assumption 1, if … F^S(t) = M_D(t)" → Σ²_FI is the explicit infimum (25) over Ψ̃ with σ²_S|FI = σ_ε²ψ̃_0²; reason: (25) is the paper’s definition of Σ²_FI; Assumption 1 enters through Ψ̃ and σ_ε > 0
--   - encoding: real MA coefficients with "∑ψ̃_n = 1" and boundary values ψ̃(e^{−iλ}) → ψ : ℕ → ℝ, convergence of partial sums (not HasSum), radial limits via limUnder; reason: the orders are real (Assumption 1(b), §9.3); ψ̃ ∈ ℓ² need not be absolutely summable; p.22 defines boundary values as radial limits
--   - encoding: inf, (x)⁺ → real sInf of attained values, max x 0; reason: Lean convention; the set is nonempty and bounded below by σ_ε²
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, Theorem 1, p.19 (proof §9.6, p.40)

import Mathlib
import Definitions.Def_InfoShareH2_Model

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **Theorem 1 (full information sharing frontier).**
SSRN 4319721 (v. 2024-01-20), Theorem 1, p.19 (proof §9.6, p.40). "Under Assumption 1, if the
retailer shares its demand information with the supplier, i.e. `F^S(t) = M_D(t)`, then
`Σ²_FI(σ) = σ_ε² + ((σ_ε − σ)⁺)²` and the optimal solution `{ψ̃_n}_{n≥0}` is given by
`ψ̃_0 = min{1, σ/σ_ε}`, `ψ̃_1 = 1 − ψ̃_0` and `ψ̃_n = 0` for `n ≥ 2`."

**Formalization Note** Stated for `σ ≥ 0` (for `σ < 0` the printed formula is false: `σ_ε = 1`,
`σ = −1` gives `Σ²_FI = 1 ≠ 5`). "The optimal solution" is read as: `ψ⋆` is feasible, attains the
infimum, and is the unique feasible policy that does (§9.6: "the unique optimal solution"). -/
theorem theorem_1 (σε σ : ℝ) (hσε : 0 < σε) (hσ : 0 ≤ σ) :
    let ψstar : ℕ → ℝ := fun n =>
      if n = 0 then min 1 (σ / σε) else if n = 1 then 1 - min 1 (σ / σε) else 0
    SigmaFIsq σε σ = σε ^ 2 + (max (σε - σ) 0) ^ 2 ∧
    ψstar ∈ PsiTilde ∧ fsVar σε ψstar ≤ σ ^ 2 ∧ invVar σε ψstar = SigmaFIsq σε σ ∧
    ∀ ψ ∈ PsiTilde, fsVar σε ψ ≤ σ ^ 2 → invVar σε ψ = SigmaFIsq σε σ → ψ = ψstar := by sorry

end InfoShareH2
