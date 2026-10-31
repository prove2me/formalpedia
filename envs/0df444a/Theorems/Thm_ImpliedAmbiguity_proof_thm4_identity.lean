-- Prove2me | Theorems.Thm_ImpliedAmbiguity_proof_thm4_identity
-- name    : ImpliedAmbiguity.proof_thm4_identity
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:05:54.205797+00:00
-- url     : https://prove2.me/theorems/ae209725-58b4-47e8-bf85-5efcbe9d5815
-- title:
--   Proof of Theorem 4 — $(\bar\theta^{-1}c-\Sigma_Rx)^\top\Sigma_R^{-1}(\bar\theta^{-1}c-\Sigma_Rx) = \bar\theta^{-2}(\mathrm{Sr}(\bar x)^2-\mathrm{Sr}(x)^2)$
-- statement:
--   Let $\Sigma_R$ be a symmetric positive definite $N\times N$ matrix, $\mu\in\mathbb R^N$, $R_f\in\mathbb R$, $x\in\mathbb R^N$, write $c = \mu-R_f\mathbf 1$, and suppose $c^\top x>0$ (14). Let $\bar\theta = c^\top x / x^\top\Sigma_R x$ (15), $\bar x = \Sigma_R^{-1}c$ and $\mathrm{Sr}$ the Sharpe ratio, and put $w = \bar\theta^{-1}c - \Sigma_R x$. Then
--
--   $$
--   \begin{aligned}
--   w^\top\Sigma_R^{-1}w &= \bar\theta^{-2}\,\mathrm{Sr}(\bar x)^2 - 2\bar\theta^{-1}\,x\cdot c + x^\top\Sigma_R x \\
--   &= \bar\theta^{-2}\,\mathrm{Sr}(\bar x)^2 - x^\top\Sigma_R x
--   = \bar\theta^{-2}\bigl(\mathrm{Sr}(\bar x)^2 - \mathrm{Sr}(x)^2\bigr),
--   \end{aligned}
--   $$
--
--   and consequently
--
--   $$
--   \frac{w^\top\Sigma_R^{-1}w}{c^\top\Sigma_R^{-1}c} = \frac1{\bar\theta^2}\left(1 - \left(\frac{\mathrm{Sr}(x)}{\mathrm{Sr}(\bar x)}\right)^2\right).
--   $$
--
--   This identity turns the minimizer and minimum of Lemma 4 (with $S=\Sigma=\Sigma_R$) into the closed forms (24) and (25) of Theorem 4.
--
--   Differences from the source:
--   - encoding: assets 1..N, µ − R_f1, Σ_R ∈ S^N_++, Sr, x̄ → `Fin N`, `excessReturn μ Rf`, `Matrix.PosDef`, `sharpe`, `tangency`; reason: Lean convention; same instances.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), proof of Theorem 4, displays after (37), p.43

import Mathlib
import Definitions.Def_ImpliedAmbiguity_excessReturn
import Definitions.Def_ImpliedAmbiguity_thetaBar
import Definitions.Def_ImpliedAmbiguity_sharpe
import Definitions.Def_ImpliedAmbiguity_tangency

open Matrix

namespace ImpliedAmbiguity

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
proof of Theorem 4, p.43: "Note here that (θ̄⁻¹(µ − R_f1) − Σ_Rx)ᵀΣ_R⁻¹(θ̄⁻¹(µ − R_f1) − Σ_Rx) is
equal to θ̄⁻²(Sr(x̄))² − 2θ̄⁻¹x·(µ − R_f1) + xᵀΣ_Rx = θ̄⁻²(Sr(x̄))² − xᵀΣ_Rx
= θ̄⁻²((Sr(x̄))² − (Sr(x))²). Thus,
(θ̄⁻¹(µ − R_f1) − Σ_Rx)ᵀΣ_R⁻¹(θ̄⁻¹(µ − R_f1) − Σ_Rx) / (µ − R_f1)ᵀΣ_R⁻¹(µ − R_f1)
= (1/θ̄²)(1 − (Sr(x)/Sr(x̄))²)."

All four equalities of the chain are stated, under the hypotheses of Theorem 4 that the proof
uses there: `Σ_R` positive definite and (14).

**Formalization Note.** `µ − R_f1` is `excessReturn μ Rf` (named `c`), `x · (µ − R_f1)` is
`x ⬝ᵥ c`, `θ̄` is `thetaBar` ((15)), `Sr` is `sharpe`, `x̄` is `tangency`. -/
theorem proof_thm4_identity {N : ℕ} (SigmaR : Matrix (Fin N) (Fin N) ℝ) (hSigmaR : SigmaR.PosDef)
    (μ : Fin N → ℝ) (Rf : ℝ) (x : Fin N → ℝ)
    (h14 : 0 < excessReturn μ Rf ⬝ᵥ x) :
    let c := excessReturn μ Rf
    let θbar := thetaBar SigmaR c x
    let w := θbar⁻¹ • c - SigmaR *ᵥ x
    let SrBar := sharpe SigmaR c (tangency SigmaR c)
    let Sr := sharpe SigmaR c x
    w ⬝ᵥ (SigmaR⁻¹ *ᵥ w) =
        θbar⁻¹ ^ 2 * SrBar ^ 2 - 2 * θbar⁻¹ * (x ⬝ᵥ c) + x ⬝ᵥ (SigmaR *ᵥ x) ∧
    θbar⁻¹ ^ 2 * SrBar ^ 2 - 2 * θbar⁻¹ * (x ⬝ᵥ c) + x ⬝ᵥ (SigmaR *ᵥ x) =
        θbar⁻¹ ^ 2 * SrBar ^ 2 - x ⬝ᵥ (SigmaR *ᵥ x) ∧
    θbar⁻¹ ^ 2 * SrBar ^ 2 - x ⬝ᵥ (SigmaR *ᵥ x) = θbar⁻¹ ^ 2 * (SrBar ^ 2 - Sr ^ 2) ∧
    (w ⬝ᵥ (SigmaR⁻¹ *ᵥ w)) / (c ⬝ᵥ (SigmaR⁻¹ *ᵥ c)) = 1 / θbar ^ 2 * (1 - (Sr / SrBar) ^ 2) := by sorry

end ImpliedAmbiguity
