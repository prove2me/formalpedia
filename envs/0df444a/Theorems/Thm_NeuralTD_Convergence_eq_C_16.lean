-- Prove2me | Theorems.Thm_NeuralTD_Convergence_eq_C_16
-- name    : NeuralTD.Convergence.eq_C_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:17.183847+00:00
-- url     : https://prove2.me/theorems/d76b4797-613a-4c1e-9745-e6e5fe7bc867
-- title:
--   (C.16), p. 32 — one-point monotonicity: (ḡ0(W) − ḡ0(W′))ᵀ(W − W′) ≥ (1 − γ)·E_µ[(Q̂0(x; W) − Q̂0(x; W′))²], posed for every pair
-- statement:
--   Let $\mu$ be a sampling law, $0 \le \gamma < 1$, and fix any $b \in \mathbb R^m$ and $W(0) \in \mathbb R^{md}$. For all parameters $W, W' \in \mathbb R^{md}$,
--   $$\big(\bar g_0(W) - \bar g_0(W')\big)^\top (W - W') \ge (1-\gamma)\,\mathbb E_\mu\Big[\big(\widehat Q_0(x;W) - \widehat Q_0(x;W')\big)^2\Big].$$
--
--   Because $\widehat Q_0$ is linear in $W$, the linearized TD direction is monotone with modulus $1-\gamma$ in the $\mu$-norm of the induced functions; this is the inequality the paper calls the key to its convergence result.
--
--   **Formalization Note.** The paper writes the inequality at the pair $(W(t), W^*)$; its derivation uses only linearity of $\widehat Q_0$ in $W$ and the equality of the marginal laws of $x$ and $x'$, so it is posed for every pair, which contains the printed case.
-- source:
--   Cai, Yang, Lee, Wang, Neural temporal-difference and Q-learning provably converge to global optima, arXiv:1905.10027v2, p. 32, (C.16) (with the Cauchy–Schwarz display that follows it, pp. 32–33)

import Mathlib
import Definitions.Def_NeuralTD_Convergence_Setting

namespace NeuralTD.Convergence

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

/-- (C.16), p. 32: one-point monotonicity of the linearized population semigradient,
`(ḡ₀(W) − ḡ₀(W′))ᵀ(W − W′) ≥ (1 − γ) E_μ[(Q̂₀(x; W) − Q̂₀(x; W′))²]`, for every pair `W, W′`. -/
theorem eq_C_16 {m d : ℕ} (γ rbar : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : Measure (Sample d))
    (hμ : IsSamplingLaw d rbar μ) (b : Fin m → ℝ) (W0 W W' : Param m d) :
    (1 - γ) * ∫ ξ, (Qlin b W0 W ξ.1 - Qlin b W0 W' ξ.1) ^ 2 ∂μ ≤
      ⟪gbarLin γ μ b W0 W - gbarLin γ μ b W0 W', W - W'⟫ := by sorry

end NeuralTD.Convergence
