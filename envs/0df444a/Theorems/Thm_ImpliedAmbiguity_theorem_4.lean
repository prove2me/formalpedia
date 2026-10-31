-- Prove2me | Theorems.Thm_ImpliedAmbiguity_theorem_4
-- name    : ImpliedAmbiguity.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:06:41.242402+00:00
-- url     : https://prove2.me/theorems/432a9c59-822d-4a4f-bd47-9104919c05fd
-- title:
--   Theorem 4 (Implied ambiguity) (corrected: requires $v^\theta\neq0$ for every $\theta>0$) — $\eta^\theta$ is minimized on $(0,\bar\theta)$ at $\theta^*=\bar\theta/(1+q)$ with value $2q/(1-q)$
-- statement:
--   Let $\Sigma_R$ be a symmetric positive definite $N\times N$ matrix (the covariance matrix of the risky asset returns), $\mu\in\mathbb R^N$ the expected returns, $R_f\in\mathbb R$ the risk-free return and $x\in\mathbb R^N$ a portfolio of risky assets. Write $c = \mu - R_f\mathbf 1$ and suppose
--
--   $$
--   c^\top x > 0. \tag{14}
--   $$
--
--   Let $\bar\theta = c^\top x/x^\top\Sigma_R x$ (15), $v^\theta = \theta^{-1}\Sigma_R^{-1}c - x$ (17) and $\eta^\theta = (v^\theta)^\top\Sigma_R v^\theta / x^\top\Sigma_R v^\theta$ (19). Assume moreover that $v^\theta\neq 0$ for every $\theta > 0$, i.e. $x$ is not a positive multiple of the tangency portfolio $\bar x = \Sigma_R^{-1}c$. With the Sharpe ratio $\mathrm{Sr}(y) = c^\top y/(y^\top\Sigma_R y)^{1/2}$ put
--
--   $$
--   q = \left(1 - \left(\frac{\mathrm{Sr}(x)}{\mathrm{Sr}(\bar x)}\right)^2\right)^{1/2},\qquad \theta^* = \frac{\bar\theta}{1+q}. \tag{24}
--   $$
--
--   Then, as a function of $\theta$ on $(0,\bar\theta)$:
--
--   1. $\theta^*\in(0,\bar\theta)$;
--   2. $\eta^{\theta^*}\le\eta^\theta$ for every $\theta\in(0,\bar\theta)$;
--   3. $\theta^*$ is the only minimizer of $\eta^\theta$ on $(0,\bar\theta)$;
--   4. the minimum value, the **implied ambiguity** of $x$, is
--   $$
--   \eta^{\theta^*} = \frac{2q}{1-q}. \tag{25}
--   $$
--
--   The implied ambiguity is the smallest coefficient of relative ambiguity aversion with which a smooth-ambiguity (KMM) investor with CARA utilities and jointly normal returns holds $x$ as optimal; it is an explicit, strictly decreasing function of the normalized Sharpe ratio $\mathrm{Sr}(x)/\mathrm{Sr}(\bar x)$.
--
--   Differences from the source:
--   - correction: no hypothesis on v^θ → ∀ θ > 0, v^θ ≠ 0 (Lemma 4's hypothesis, by which the paper proves the theorem); reason: the printed theorem is false when x is a positive multiple of x̄ — N = 1, Σ_R = 1, µ = 2, R_f = 1, x = 1 satisfies (14), θ̄ = 1, η^θ = 1/θ − 1 has no minimum on (0, 1), and (24) gives θ* = 1 ∉ (0, θ̄).
--   - reading: "η^θ is minimized when θ is equal to θ*" → θ* ∈ (0, θ̄), θ* minimizes η^θ on (0, θ̄), and it is the only minimizer there; reason: Lemma 4, which the paper's proof applies, asserts a unique minimizer in (0, θ̄).
--   - encoding: Σ_R ∈ S^N_++, µ − R_f1, θ̄, η^θ defined for v^θ ≠ 0, Sr on ℝᴺ∖{0}, (·)^{1/2}, "Let θ > 0 and suppose (16)" → `Matrix.PosDef`, `excessReturn μ Rf`, `thetaBar`, total `etaTheta` minimized over exactly `Set.Ioo 0 θ̄`, total `sharpe`, `Real.sqrt`, θ bound inside `IsMinOn`; reason: Lean convention; on (0, θ̄) every quantity is the paper's.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), Theorem 4, eqs. (24)–(25), pp.21–22; correction from Appendix C, Lemma 4, p.41

import Mathlib
import Definitions.Def_ImpliedAmbiguity_excessReturn
import Definitions.Def_ImpliedAmbiguity_thetaBar
import Definitions.Def_ImpliedAmbiguity_vTheta
import Definitions.Def_ImpliedAmbiguity_etaTheta
import Definitions.Def_ImpliedAmbiguity_sharpe
import Definitions.Def_ImpliedAmbiguity_tangency

open Matrix

namespace ImpliedAmbiguity

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
Theorem 4 (Implied ambiguity), pp.21–22: Let `Σ_R ∈ S^N_++`, `µ ∈ R^N`, `R_f ∈ R` and `x ∈ R^N`,
and suppose (14) `(µ − R_f1)ᵀx > 0`. Define `θ̄` as in (15) and `η^θ` as in (19). Then, as a
function of `θ` defined on `(0, θ̄)`, `η^θ` is minimized when `θ` is equal to
(24) `θ* ≡ θ̄ / (1 + (1 − (Sr(x)/Sr(x̄))²)^{1/2})`, and the minimized value is
(25) `η^{θ*} = 2(1 − (Sr(x)/Sr(x̄))²)^{1/2} / (1 − (1 − (Sr(x)/Sr(x̄))²)^{1/2})`.

**Correction.** The printed theorem is false when `x` is a positive multiple of the tangency
portfolio `x̄ = Σ_R⁻¹(µ − R_f1)` (e.g. `N = 1`, `Σ_R = 1`, `µ = 2`, `R_f = 1`, `x = 1`: `θ̄ = 1`,
`η^θ = 1/θ − 1` on `(0, 1)` has no minimum and (24) gives `θ* = 1 ∉ (0, θ̄)`). The hypothesis `hv`
is Lemma 4's hypothesis "there is no θ > 0 for which v^θ = 0" (p.41), by which the paper proves
Theorem 4.

"η^θ is minimized when θ = θ*" is read as: `θ* ∈ (0, θ̄)`, `θ*` minimizes `η^θ` on `(0, θ̄)`, and
it is the only minimizer there (Lemma 4: "a unique θ").

**Formalization Note.** `S^N_++` is `Matrix.PosDef`; `µ − R_f1` is `excessReturn μ Rf`; `θ̄`,
`v^θ`, `η^θ`, `Sr`, `x̄` are `thetaBar`, `vTheta`, `etaTheta`, `sharpe`, `tangency`; `(·)^{1/2}` is
`Real.sqrt`. `η^θ` is a total function of `θ` and is minimized over exactly `Set.Ioo 0 θ̄`. -/
theorem theorem_4 {N : ℕ} (SigmaR : Matrix (Fin N) (Fin N) ℝ) (hSigmaR : SigmaR.PosDef)
    (μ : Fin N → ℝ) (Rf : ℝ) (x : Fin N → ℝ)
    (h14 : 0 < excessReturn μ Rf ⬝ᵥ x)
    (hv : ∀ θ : ℝ, 0 < θ → vTheta SigmaR (excessReturn μ Rf) x θ ≠ 0) :
    let c := excessReturn μ Rf
    let θbar := thetaBar SigmaR c x
    let q := Real.sqrt (1 - (sharpe SigmaR c x / sharpe SigmaR c (tangency SigmaR c)) ^ 2)
    let θstar := θbar / (1 + q)
    θstar ∈ Set.Ioo 0 θbar ∧
    IsMinOn (etaTheta SigmaR c x) (Set.Ioo 0 θbar) θstar ∧
    (∀ θ ∈ Set.Ioo 0 θbar, etaTheta SigmaR c x θ = etaTheta SigmaR c x θstar → θ = θstar) ∧
    etaTheta SigmaR c x θstar = 2 * q / (1 - q) := by sorry

end ImpliedAmbiguity
