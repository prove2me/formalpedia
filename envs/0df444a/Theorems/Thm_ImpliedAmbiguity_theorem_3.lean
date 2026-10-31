-- Prove2me | Theorems.Thm_ImpliedAmbiguity_theorem_3
-- name    : ImpliedAmbiguity.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:07:09.408269+00:00
-- url     : https://prove2.me/theorems/3d7c235b-15f6-4272-9e63-7cf6a51e401c
-- title:
--   Theorem 3 (Construction of ambiguity) — $0\le\Sigma_M^\theta\le\Sigma_R$, $\eta^\theta>0$, and $x$ is optimal
-- statement:
--   Let $\Sigma_R$ be a symmetric positive definite $N\times N$ matrix, $\mu\in\mathbb R^N$, $R_f\in\mathbb R$ and $x\in\mathbb R^N$, and write $c = \mu - R_f\mathbf 1$. Suppose
--
--   $$
--   c^\top x > 0, \tag{14}
--   $$
--
--   let $\bar\theta = c^\top x / x^\top\Sigma_R x$ as in (15), and let $\theta$ satisfy $0 < \theta < \bar\theta$ (16). Let $v^\theta = \theta^{-1}\Sigma_R^{-1}c - x$ (17) and suppose $v^\theta \neq 0$. Define $\Sigma_M^\theta$ and $\eta^\theta$ by (18) and (19). Then
--
--   1. $\Sigma_M^\theta$ is positive semidefinite, $0 \le \Sigma_M^\theta$;
--   2. $\Sigma_R - \Sigma_M^\theta$ is positive semidefinite, $\Sigma_M^\theta \le \Sigma_R$;
--   3. $\eta^\theta > 0$;
--   4. $$x = \frac1\theta\bigl(\Sigma_R + \eta^\theta\Sigma_M^\theta\bigr)^{-1} c. \tag{22}$$
--
--   So $\Sigma_M^\theta$ is an admissible second-order belief, $\eta^\theta$ the coefficient of relative ambiguity aversion of an ambiguity-averse investor, and $x$ is optimal for that investor by the first-order condition (8).
--
--   **Formalization Note** $\le$ between symmetric matrices is the Loewner order, $A\le B$ iff $B-A$ is positive semidefinite (p.10).
--
--   Differences from the source:
--   - encoding: $\Sigma_R\in\mathcal S^N_{++}$, $\Sigma_1\le\Sigma_2$, assets $1,\dots,N$, $\mu-R_f\mathbf 1$ → `Matrix.PosDef`, `(Σ₂ - Σ₁).PosSemidef`, `Fin N`, `excessReturn μ Rf`; reason: Lean convention; same instances.
--   - encoding: $\Sigma_M^\theta$, $\eta^\theta$ defined when $v^\theta\neq0$ → total functions `sigmaMTheta`, `etaTheta`, with $v^\theta\neq0$ kept as a hypothesis; reason: the hypothesis excludes exactly the undefined case.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), Theorem 3, p.19

import Mathlib
import Definitions.Def_ImpliedAmbiguity_excessReturn
import Definitions.Def_ImpliedAmbiguity_thetaBar
import Definitions.Def_ImpliedAmbiguity_vTheta
import Definitions.Def_ImpliedAmbiguity_sigmaMTheta
import Definitions.Def_ImpliedAmbiguity_etaTheta

open Matrix

namespace ImpliedAmbiguity

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
Theorem 3 (Construction of ambiguity), p.19: Let `Σ_R ∈ S^N_++`, `µ ∈ R^N`, `R_f ∈ R` and
`x ∈ R^N` with (14) `(µ − R_f1)ᵀx > 0`; let `θ > 0` with (16) `θ < θ̄` ((15)), and suppose
`v^θ ≠ 0` ((17)). Then, with `Σ^θ_M` and `η^θ` as in (18), (19): `0 ≤ Σ^θ_M ≤ Σ_R`, `η^θ > 0`, and
(22) `x = (1/θ)(Σ_R + η^θΣ^θ_M)⁻¹(µ − R_f1)`.

**Formalization Note.** `S^N_++` is `Matrix.PosDef` (symmetric positive definite). The Loewner
order `A ≤ B` ("B − A ∈ S^N_+", p.10) is `(B - A).PosSemidef`; `0 ≤ Σ^θ_M` is
`(sigmaMTheta …).PosSemidef`. Assets are indexed by `Fin N`; `µ − R_f1` is `excessReturn μ Rf`. The
inverse in (22) is Mathlib's matrix inverse. -/
theorem theorem_3 {N : ℕ} (SigmaR : Matrix (Fin N) (Fin N) ℝ) (hSigmaR : SigmaR.PosDef)
    (μ : Fin N → ℝ) (Rf : ℝ) (x : Fin N → ℝ)
    (h14 : 0 < excessReturn μ Rf ⬝ᵥ x)
    (θ : ℝ) (hθ : 0 < θ) (h16 : θ < thetaBar SigmaR (excessReturn μ Rf) x)
    (hv : vTheta SigmaR (excessReturn μ Rf) x θ ≠ 0) :
    (sigmaMTheta SigmaR (excessReturn μ Rf) x θ).PosSemidef ∧
    (SigmaR - sigmaMTheta SigmaR (excessReturn μ Rf) x θ).PosSemidef ∧
    0 < etaTheta SigmaR (excessReturn μ Rf) x θ ∧
    x = (1 / θ) • ((SigmaR + etaTheta SigmaR (excessReturn μ Rf) x θ •
          sigmaMTheta SigmaR (excessReturn μ Rf) x θ)⁻¹ *ᵥ excessReturn μ Rf) := by sorry

end ImpliedAmbiguity
