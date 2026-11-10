-- Prove2me | Theorems.Thm_LRTempElim_proposition_A_4
-- name    : LRTempElim.proposition_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:09.473572+00:00
-- url     : https://prove2.me/theorems/d94eb9d0-b7fd-41ef-9794-f4c474536c18
-- title:
--   Proposition A.4: overlap lower bound $C_{\mathrm{NCE}}\ge 2/\omega-2$ for balanced logistic DRE
-- statement:
--   Let $P=p\,\mu$ and $Q=q\,\mu$ be probability laws with densities $p,q\ge0$ against a reference measure $\mu$, $\nu=\tfrac12(P+Q)$, $\eta=p/(p+q)$, $w=\eta(1-\eta)$, and
--   $$
--   H_{\mathrm{NCE}}=\mathbb E_\nu[w(X)\phi(X)\phi(X)^\top],\qquad \omega(P,Q)=\int\frac{2p(x)q(x)}{p(x)+q(x)}\,dx .
--   $$
--   Let $\phi:\mathcal X\to\mathbb R^k$, $k\ge1$, have constant first coordinate $\phi^\top e_0=1$, $e_0=(1,0,\dots,0)^\top$. Assume $\ell^\star=\log(p/q)=\theta_*^\top\phi$, a finite $\Sigma=\mathbb E_\nu[\phi\phi^\top]$ and $H_{\mathrm{NCE}}\succ0$. Let $V_{\mathrm{NCE}}=H_{\mathrm{NCE}}^{-1}\,\mathrm{Var}(g)\,H_{\mathrm{NCE}}^{-1}$ be the M-estimator sandwich at the balanced pair gradient $g(W)=\tfrac12[(\eta(X_1)-1)\phi(X_1)+\eta(X_0)\phi(X_0)]$, $W\sim Q\otimes P$, and $C_{\mathrm{NCE}}=\operatorname{tr}(\Sigma V_{\mathrm{NCE}})$. Then
--   $$
--   V_{\mathrm{NCE}}=\tfrac12H_{\mathrm{NCE}}^{-1}-2e_0e_0^\top,\qquad C_{\mathrm{NCE}}=\tfrac12\operatorname{tr}(\Sigma H_{\mathrm{NCE}}^{-1})-2,
--   $$
--   and
--   $$
--   C_{\mathrm{NCE}}\ge\frac2{\omega(P,Q)}-2,\qquad C_{\mathrm{NCE}}\ge2(k-1)+2\Big(\frac1{\omega(P,Q)}-1\Big).
--   $$
--   At $P=Q$, $\omega=1$ and $C_{\mathrm{NCE}}=2(k-1)$, so the dimension-corrected bound is attained.
--
--   This is the distribution-free form of the logistic penalty for weak overlap: the asymptotic risk coefficient of balanced logistic DRE is at least of order $1/\omega$.
--
--   **Formalization Note** "Finite $\Sigma$" is that every feature coordinate is in $L^2(\nu)$; $P=Q$ is $p=q$ $\mu$-almost everywhere.
--
--   Differences from the source:
--   - generalization: densities on X ⊆ ℝᵈ with respect to a common reference measure (§2.2) → an arbitrary measurable space X with an arbitrary reference measure μ; reason: the proof uses only integrals against μ; X ⊆ ℝᵈ is a special case
--   - reading: "the asymptotic covariance of √N(θ̂ − θ∗)" under the usual local M-estimation conditions → the M-estimator sandwich V_NCE = H⁻¹ Var(g) H⁻¹ (`logisticV`); the M-estimation conditions are not hypotheses; reason: the proof identifies the asymptotic covariance with this sandwich by the standard formula; the conditions serve only that identification, which is the same reading the goal theorem uses for C_NCE(a)
--   - encoding: ℓ⋆ = log(p/q) = θ∗⊤ϕ → ν-a.e.: p > 0, q > 0 and Real.log (p/q) = θ∗⊤ϕ; reason: ℓ⋆ is finite exactly on the common support; Lean's log 0 = 0 would otherwise admit spurious instances
--   - encoding: p, q densities of probability laws → measurable, nonnegative, integrable, with integral 1; reason: the meaning of a probability density
--   - encoding: a finite Σ → every feature coordinate in L²(ν); reason: Σ = E_ν[ϕϕ⊤] is finite iff each coordinate is square-integrable
--   - encoding: At P = Q → p = q μ-a.e.; reason: equality of the laws
--   - encoding: k features with ϕ⊤e₀ = 1 → `NeZero k` and ϕ x 0 = 1, e₀ = Pi.single 0 1; reason: 0-based indices; k ≥ 1 is needed for e₀ to exist
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), §A.2.1 standing conditions (33) and Proposition A.4, eqs. (34)–(36), pp.16–17 (pdf pp.18–19)

import Mathlib
import Definitions.Def_LRTempElim_Logistic

open MeasureTheory ProbabilityTheory Matrix

namespace LRTempElim

/-- **Proposition A.4** (Overlap lower bound). Chen, Wu, Yang, Zeng, *Likelihood-Ratio Learning
under Weak Overlap via Analytic Temporal Elimination*, STOC 2027 submission (manuscript of
2026-11-03, sha256 eee65139…), §A.2.1 and Proposition A.4, eqs. (33)–(36), pp.16–17
(pdf pp.18–19).

Standing conditions (p.16): "Let `η(x) = p(x)/(p(x) + q(x))`, `w(x) = η(x)(1 − η(x))`, and
`H_NCE = E_ν[w(X)ϕ(X)ϕ(X)⊤]`, `ω(P, Q) = ∫ 2p(x)q(x)/(p(x) + q(x)) dx = 4E_ν[w(X)]`. (33) The
constant feature is the first coordinate, so `ϕ⊤e₀ = 1` and `e₀ = (1, 0, …, 0)⊤`. Assume
`ℓ⋆ = θ∗⊤ϕ`, a finite Σ, `H_NCE ≻ 0`, and that the balanced logistic estimator with N samples per
class (equivalently N endpoint pairs) satisfies the usual local M-estimation conditions. Write
`Σ = E_ν[ϕϕ⊤]`."

Statement: "Under the stated conditions, the asymptotic covariance of `√N(θ̂ − θ∗)` is
`V_NCE = ½H_NCE⁻¹ − 2e₀e₀⊤`, `C_NCE := tr(ΣV_NCE) = ½ tr(ΣH_NCE⁻¹) − 2`. (34) Moreover,
`C_NCE ≥ 2/ω(P, Q) − 2`, (35) and `C_NCE ≥ 2(k − 1) + 2(1/ω(P, Q) − 1)`. (36) At `P = Q`, `ω = 1`
and `C_NCE = 2(k − 1)`, so the dimension-corrected bound is attained."

**Formalization Note.**
* `P = p·μ`, `Q = q·μ` with measurable densities `p, q ≥ 0` of total mass 1 against a common
  reference measure `μ` on an arbitrary measurable space `X` (the paper's `X ⊆ ℝᵈ` is a special
  case); `ν = (P + Q)/2` (`nuD`), pair law `Q ⊗ P` (`pairLawD`).
* "The asymptotic covariance of `√N(θ̂ − θ∗)`" is the M-estimator sandwich
  `V_NCE = H⁻¹ Var(g) H⁻¹` at the gradient `g` of (37), which the proof identifies with it
  (`logisticV`); the local M-estimation conditions serve only that identification and are not
  hypotheses here.
* `ℓ⋆ = log(p/q) = θ∗⊤ϕ` is assumed `ν`-a.e., together with `p, q > 0` there (`ℓ⋆` is finite only
  on the common support, §2.2).
* "Finite Σ": every feature coordinate is in `L²(ν)`. `k ≥ 1` (`NeZero k`), `ϕ x 0 = 1`.
* `e₀e₀⊤ = vecMulVec e₀ e₀` with `e₀ = Pi.single 0 1`. "At `P = Q`" is `p = q` `μ`-a.e. -/
theorem proposition_A_4 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p q : X → ℝ) (hp_meas : Measurable p) (hq_meas : Measurable q)
    (hp_nonneg : ∀ x, 0 ≤ p x) (hq_nonneg : ∀ x, 0 ≤ q x)
    (hp_int : Integrable p μ) (hq_int : Integrable q μ)
    (hp_one : ∫ x, p x ∂μ = 1) (hq_one : ∫ x, q x ∂μ = 1)
    {k : ℕ} [NeZero k] (ϕ : X → Fin k → ℝ) (hϕ_meas : Measurable ϕ)
    (hϕ0 : ∀ x, ϕ x 0 = 1)
    (hSigma : ∀ i, MemLp (fun x => ϕ x i) 2 (nuD μ p q))
    (θs : Fin k → ℝ)
    (hspec : ∀ᵐ x ∂(nuD μ p q), 0 < p x ∧ 0 < q x ∧ Real.log (p x / q x) = θs ⬝ᵥ ϕ x)
    (hH : (logisticHess (etaD p q) ϕ (nuD μ p q)).PosDef) :
    let H := logisticHess (etaD p q) ϕ (nuD μ p q)
    let Sm := secondMoment ϕ (nuD μ p q)
    let V := logisticV (etaD p q) ϕ (nuD μ p q) (pairLawD μ p q)
    let C := logisticC (etaD p q) ϕ (nuD μ p q) (pairLawD μ p q)
    let e₀ : Fin k → ℝ := Pi.single 0 1
    let ω := overlap μ p q
    V = (1 / 2 : ℝ) • H⁻¹ - (2 : ℝ) • vecMulVec e₀ e₀ ∧
      C = 1 / 2 * Matrix.trace (Sm * H⁻¹) - 2 ∧
      2 / ω - 2 ≤ C ∧
      2 * ((k : ℝ) - 1) + 2 * (1 / ω - 1) ≤ C ∧
      ((∀ᵐ x ∂μ, p x = q x) → ω = 1 ∧ C = 2 * ((k : ℝ) - 1)) := by sorry

end LRTempElim
