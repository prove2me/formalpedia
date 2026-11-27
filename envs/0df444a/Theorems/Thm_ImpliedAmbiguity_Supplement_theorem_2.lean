-- Prove2me | Theorems.Thm_ImpliedAmbiguity_Supplement_theorem_2
-- name    : ImpliedAmbiguity.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:03:19.735106+00:00
-- url     : https://prove2.me/theorems/74d3df70-dd9c-5d06-9f68-fe8e174873d5
-- title:
--   Theorem 2 (Necessary conditions of an optimal portfolio) (corrected: (14) needs $\mu\ne R_f\mathbf 1$, (16) needs $v^\theta\ne0$) — (14), (16), (20), (21)
-- statement:
--   Let $\Sigma_R \in \mathcal S^N_{++}$ be the total covariance matrix of the $N$ risky asset returns, $\mu \in \mathbb R^N$ the expected returns, $R_f\in\mathbb R$ the risk-free return, $\theta > 0$ a coefficient of absolute risk aversion, $\Sigma_M \in \mathcal S^N_+$ a second-order belief with $\Sigma_M \le \Sigma_R$ (that is, $\Sigma_R - \Sigma_M$ is positive semidefinite), $\eta \ge 0$ a coefficient of relative ambiguity aversion, and $x \in \mathbb R^N$ a portfolio that is optimal in the sense of (8):
--
--   $$
--   x = \frac1\theta\,(\Sigma_R + \eta\Sigma_M)^{-1}(\mu - R_f\mathbf 1).
--   $$
--
--   Write $\bar\theta = (\mu-R_f\mathbf 1)^\top x / x^\top\Sigma_R x$ (15), $v^\theta = \theta^{-1}\Sigma_R^{-1}(\mu - R_f\mathbf 1) - x$ (17), and, when $v^\theta \ne 0$,
--
--   $$
--   \Sigma_M^\theta = \frac{(\Sigma_R v^\theta)(\Sigma_R v^\theta)^\top}{(v^\theta)^\top\Sigma_R v^\theta}, \qquad \eta^\theta = \frac{(v^\theta)^\top\Sigma_R v^\theta}{x^\top\Sigma_R v^\theta}. \tag{18, 19}
--   $$
--
--   Then:
--
--   1. if $\mu \neq R_f\mathbf 1$, then $(\mu - R_f\mathbf 1)^\top x > 0$ (14);
--   2. if $v^\theta \neq 0$, then $\theta < \bar\theta$ (16), $\eta\Sigma_M \ge \eta^\theta\Sigma_M^\theta$ in the Loewner order (20), and $\eta \ge \eta^\theta$ (21).
--
--   These are necessary conditions for $x$ to be optimal: the expected excess return of $x$ is positive, $\bar\theta$ bounds the coefficient of absolute risk aversion from above, and $\eta^\theta\Sigma^\theta_M$ and $\eta^\theta$ bound the scaled second-order belief and the coefficient of relative ambiguity aversion from below. Theorem 3 shows the lower bounds are attained.
--
--   **Formalization Note** Assets are indexed by `Fin N`; $\mathcal S^N_{++}$ is `Matrix.PosDef`, and $A \ge B$ is positive semidefiniteness of $A - B$. $\bar\theta$, $v^\theta$, $\Sigma^\theta_M$, $\eta^\theta$ are the published definitions of the base mission, which use Lean's total division ($a/0 = 0$); under $v^\theta \ne 0$ every denominator involved is positive. Under the other hypotheses, $v^\theta = \eta\Sigma_R^{-1}\Sigma_M x$, and $v^\theta\ne 0$ implies $\mu \ne R_f\mathbf 1$.
--
--   Differences from the source:
--   - correction: (14) is asserted under the hypotheses of the theorem alone → Lean asserts (14) under the extra hypothesis $\mu - R_f\mathbf 1 \neq 0$; reason: if $\mu = R_f\mathbf 1$ then (8) gives $x = 0$ and $(\mu-R_f\mathbf 1)^\top x = 0$ (e.g. $N=1$, $\Sigma_R=1$, $\Sigma_M=0$, $\eta=0$, $\theta=1$, $\mu=R_f$); the proof (p.40) derives (14) from $v^\theta\neq0$, and $\mu\ne R_f\mathbf 1$ is weaker than $v^\theta\ne0$ and necessary.
--   - correction: (16) is asserted under the hypotheses of the theorem alone → Lean asserts (16) under $v^\theta \neq 0$, the printed hypothesis of (20)–(21); reason: with $N=1$, $\Sigma_R=1$, $\Sigma_M=0$, $\eta=0$, $\theta=1$, $\mu-R_f=1$, $x=1$, (8) holds and $\bar\theta = 1 = \theta$; under the hypotheses $\theta<\bar\theta$ holds exactly when $v^\theta\ne0$, and the proof (p.40) begins "Since $v^\theta \neq 0$".
--   - encoding: $\Sigma_1 \ge \Sigma_2$ iff $\Sigma_1-\Sigma_2\in\mathcal S^N_+$ → `(A - B).PosSemidef`; reason: the paper's definition (p.10); same instances.
--   - encoding: (15), (18), (19) defined with divisions → total functions with Lean's $a/0=0$; reason: Lean convention; every conclusion using them is asserted only under $v^\theta\ne0$, where the denominators are positive.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), Theorem 2, pp.18–19 (eq. (8), p.12; eq. (14)–(21)); proof in Appendix C, p.40

import Mathlib
import Definitions.Def_ImpliedAmbiguity_excessReturn
import Definitions.Def_ImpliedAmbiguity_thetaBar
import Definitions.Def_ImpliedAmbiguity_vTheta
import Definitions.Def_ImpliedAmbiguity_sigmaMTheta
import Definitions.Def_ImpliedAmbiguity_etaTheta

open Matrix

namespace ImpliedAmbiguity.Supplement

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
Theorem 2 (Necessary conditions of an optimal portfolio), pp.18–19: let `Σ_R ∈ S^N_++`,
`µ ∈ R^N`, `R_f ∈ R`, `θ > 0`, `Σ_M ∈ S^N_+`, `η ≥ 0`, `x ∈ R^N` with `Σ_M ≤ Σ_R` and (8)
`x = (1/θ)(Σ_R + ηΣ_M)⁻¹(µ − R_f1)` (p.12). Then (14) `(µ − R_f1)ᵀx > 0`, (16) `θ < θ̄` with `θ̄`
as in (15), and, if `v^θ ≠ 0` ((17)), with `Σ^θ_M`, `η^θ` as in (18), (19):
(20) `ηΣ_M ≥ η^θΣ^θ_M` and (21) `η ≥ η^θ`.

**Formalization Note (correction).** As printed, (14) fails when `µ = R_f1` (then (8) gives
`x = 0`) and (16) fails whenever `v^θ = 0` (e.g. `N = 1`, `Σ_R = 1`, `Σ_M = 0`, `θ = 1`,
`µ − R_f = 1`, `x = 1`: (8) holds, `θ̄ = 1 = θ`). The proof (Appendix C, p.40) starts "Since
`v^θ ≠ 0`". This statement asserts (14) under `µ − R_f1 ≠ 0` and (16), (20), (21) under
`v^θ ≠ 0`; under the other hypotheses `v^θ ≠ 0` implies `µ − R_f1 ≠ 0`, and each added
hypothesis is necessary for its conclusion. `S^N_++` is `Matrix.PosDef`; the Loewner order
`A ≥ B` is `(A - B).PosSemidef` (p.10). `µ − R_f1` is `excessReturn μ Rf`; θ̄, v^θ, Σ^θ_M, η^θ are
the base mission's `thetaBar`, `vTheta`, `sigmaMTheta`, `etaTheta`. -/
theorem theorem_2 {N : ℕ} (SigmaR : Matrix (Fin N) (Fin N) ℝ) (hSigmaR : SigmaR.PosDef)
    (μ : Fin N → ℝ) (Rf : ℝ) (θ : ℝ) (hθ : 0 < θ)
    (SigmaM : Matrix (Fin N) (Fin N) ℝ) (hSigmaM : SigmaM.PosSemidef)
    (η : ℝ) (hη : 0 ≤ η) (x : Fin N → ℝ)
    (hMR : (SigmaR - SigmaM).PosSemidef)
    (h8 : x = (1 / θ) • ((SigmaR + η • SigmaM)⁻¹ *ᵥ excessReturn μ Rf)) :
    (excessReturn μ Rf ≠ 0 → 0 < excessReturn μ Rf ⬝ᵥ x) ∧
    (vTheta SigmaR (excessReturn μ Rf) x θ ≠ 0 →
      θ < thetaBar SigmaR (excessReturn μ Rf) x ∧
      (η • SigmaM - etaTheta SigmaR (excessReturn μ Rf) x θ •
        sigmaMTheta SigmaR (excessReturn μ Rf) x θ).PosSemidef ∧
      etaTheta SigmaR (excessReturn μ Rf) x θ ≤ η) := by sorry

end ImpliedAmbiguity.Supplement
