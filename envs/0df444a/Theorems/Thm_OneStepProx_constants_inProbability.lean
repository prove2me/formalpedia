-- Prove2me | Theorems.Thm_OneStepProx_constants_inProbability
-- name    : OneStepProx.constants_inProbability
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:09:50.5169+00:00
-- url     : https://prove2.me/theorems/dcc3be0b-0b3b-4cb2-b536-593209a9e1f5
-- title:
--   Proof of Theorem 2.1, p.7 — under (ii), $\sqrt{\lambda_{\max}(C_n)/\lambda_{\min}(C_n)}$ converges in probability and $\|C_n^{-1}\|=O_P(1)$
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space, $H\succ0$ a $d\times d$ matrix and $(C_n)$ a sequence of random $d\times d$ matrices with $C_n\succ0$ almost surely for each $n$ and $C_n^{-1}H\xrightarrow{P}I$. Then
--
--   $$
--   \sqrt{\frac{\lambda_{\max}(C_n)}{\lambda_{\min}(C_n)}}\xrightarrow{P}\sqrt{\frac{\lambda_{\max}(H)}{\lambda_{\min}(H)}}
--   \qquad\text{and}\qquad
--   \|C_n^{-1}\|=O_P(1).
--   $$
--
--   These are the two facts about the scaling matrices that the proof of Theorem 2.1 draws from assumption (ii): the Lipschitz constant of the prox stays bounded with high probability, and the factor $K\|C_n^{-1}\|$ in (2.3) is stochastically bounded.
--
--   **Formalization Note** Matrix norms are the spectral norm, which also gives the metric of the convergence in probability; any matrix norm gives the same convergence. $O_P(1)$ is `ResidualsDRO.Unified.IsBigOp` with rate $1$. `(C n ω)⁻¹` is a junk value only on the null event where $C_n$ is singular.
--
--   Differences from the source:
--   - generalization: $\sqrt{\lambda_{\max}(C_n)/\lambda_{\min}(C_n)}$ "converges in probability to some constant" → the constant is named, $\sqrt{\lambda_{\max}(H)/\lambda_{\min}(H)}$; reason: the Lean statement implies the paper's, and with it "there exists a $K$ … with probability $1-\epsilon$".
--   - generalization: measurable random matrices → no measurability of $C_n$; reason: probabilities are outer measures, which agree with $P$ on measurable events.
--   - reading: "$C_n\succ0$" → $C_n\succ0$ almost surely, for each $n$; reason: Theorem 2.1 is an almost sure statement about the random objects, and this is the weaker hypothesis.
--   - encoding: $\succ0$ → `Matrix.PosDef`; reason: it includes symmetry, as the eigenvalues in the paper's constant presuppose.
--   - encoding: $\|C_n^{-1}\|=O_P(1)$ → for every $\delta>0$ there are $M>0$, $N$ with $P(\|C_n^{-1}\|>M)\le\delta$ for $n\ge N$; reason: this is boundedness in probability, eventually in $n$.
--   - encoding: $K\|C_n^{-1}\|=O_P(1)$ for the constant $K$ → $\|C_n^{-1}\|=O_P(1)$; reason: a positive constant factor does not change $O_P(1)$.
-- source:
--   Bassett & Deride, One-Step Estimation with Scaled Proximal Methods, arXiv:2004.14521v3, proof of Theorem 2.1, p.7, "converges in probability to some constant" and "K‖Cn⁻¹‖ = OP(1) because of assumption (ii)"

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_OneStepProx_eigenRatioSqrt

open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator

namespace OneStepProx

/-- Bassett & Deride, arXiv:2004.14521v3, proof of Theorem 2.1, p.7: if `Cₙ ≻ 0` almost surely,
`H ≻ 0` and `Cₙ⁻¹H →ᴾ I`, then `√(λmax(Cₙ)/λmin(Cₙ))` converges in probability to a constant,
namely `√(λmax(H)/λmin(H))`, and `‖Cₙ⁻¹‖ = O_P(1)`.

**Formalization Note.** Matrix norms are the spectral norm (`Matrix.Norms.L2Operator`), which also
gives the metric of the convergence `Cₙ⁻¹H →ᴾ I`. `O_P(1)` is
`ResidualsDRO.Unified.IsBigOp … (fun _ => 1)`. No measurability is assumed: probabilities of
events that need not be measurable are outer measures. `(C n ω)⁻¹` is the matrix inverse, a junk
value only on the null event where `C n ω` is singular. -/
theorem constants_inProbability {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {C : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ}
    {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    (hC : ∀ n, ∀ᵐ ω ∂P, (C n ω).PosDef)
    (hii : TendstoInMeasure P (fun n ω => (C n ω)⁻¹ * H) atTop (fun _ => 1)) :
    TendstoInMeasure P (fun n ω => eigenRatioSqrt (C n ω)) atTop (fun _ => eigenRatioSqrt H) ∧
      ResidualsDRO.Unified.IsBigOp P (fun n ω => ENNReal.ofReal ‖(C n ω)⁻¹‖) (fun _ => 1) := by sorry

end OneStepProx
