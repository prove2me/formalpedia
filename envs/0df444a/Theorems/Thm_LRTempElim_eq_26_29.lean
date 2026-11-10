-- Prove2me | Theorems.Thm_LRTempElim_eq_26_29
-- name    : LRTempElim.eq_26_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:09.221668+00:00
-- url     : https://prove2.me/theorems/f7cb7162-d93b-40b6-9bf3-1d5ca008b53a
-- title:
--   Eqs. (26), (29): bridge marginal, time score, $b_t=M_t\eta'(t)$
-- statement:
--   Let $(X_0,X_1)\sim N(-a/2,1)\otimes N(a/2,1)$ and $X_t=(1-t)X_0+tX_1$. Put $\mu_t=a(t-\tfrac12)$, $c_t=(1-t)^2+t^2$, $c'_t=\frac{d}{dt}c_t$ and
--   $$
--   \eta'(t)=\Big(-\frac{a\mu_t}{c_t}+\frac{c'_t\mu_t^2}{2c_t^2}-\frac{c'_t}{2c_t},\ \ \frac a{c_t}-\frac{c'_t\mu_t}{c_t^2},\ \ \frac{c'_t}{2c_t^2}\Big).
--   $$
--   For every $a$ and every $t\in[0,1]$, with $\phi(x)=(1,x,x^2)$:
--
--   1. the bridge marginal is $P_t=N(\mu_t,c_t)$;
--   2. its time score is
--   $$
--   s_t(x)=\partial_t\log p_t(x)=\frac{a(x-\mu_t)}{c_t}+\frac{c'_t}{2c_t^2}\big((x-\mu_t)^2-c_t\big);
--   $$
--   3. $s_t=\phi^\top\eta'(t)$, i.e. the score lies in the feature span;
--   4. $b_t=M_t\eta'(t)$, where $M_t=\mathbb E[\phi(X_t)\phi(X_t)^\top]$ and $b_t=\mathbb E[J_\phi(X_t)(X_1-X_0)]$;
--   5. consequently $v_t=M_t^{-1}b_t=\eta'(t)$, and the readout is $m=\int_0^1\eta'(t)\,dt$.
--
--   These identities give the closed form of the timewise coefficients $v_t$ used in the influence-function calculation.
--
--   Differences from the source:
--   - encoding: variance c_t of N(µ_t, c_t) → `(bridgeVar t).toNNReal`; reason: Mathlib's Gaussian takes an ℝ≥0 variance; c_t ≥ 1/2 > 0, so nothing is lost
--   - encoding: time score s_t → t-derivative of the log of the Gaussian density of N(µ_t, c_t) at x; reason: the paper's definition s⋆_t = ∂_t log p_t, eq. (2)
--   - encoding: "Then b_t = M_tη′(t) and the readout is m = ∫₀¹ η′(t) dt" → the clauses b_t = M_tη′(t), v_t = η′(t) and readout = ∫₀¹ η′(t) dt; reason: v_t = M_t⁻¹b_t (41); the middle clause records the invertibility the sentence uses
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), proof of Proposition A.2, eqs. (26), (29), p.15 (pdf p.17)

import Mathlib
import Definitions.Def_LRTempElim_PathEstimator

open MeasureTheory ProbabilityTheory Matrix

namespace LRTempElim

/-- **Eqs. (26), (29)** (proof of Proposition A.2): bridge marginal, time score, and
`b_t = M_tη′(t)`. Chen, Wu, Yang, Zeng, *Likelihood-Ratio Learning under Weak Overlap via Analytic
Temporal Elimination*, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee65139…), proof of
Proposition A.2, eqs. (26), (29), p.15 (pdf p.17).

"The bridge marginal is `P_t = N(µ_t, c_t)` with `µ_t = a(t − 1/2)` and `c_t = (1 − t)² + t²`. Its
time score is `s_t(x) = a(x − µ_t)/c_t + c′_t/(2c_t²)((x − µ_t)² − c_t)`. (26)" … "For
`ϕ = (1, x, x²)`, the score (26) lies in the span for every t. Write `s_t = ϕ⊤η′(t)`. Then
`b_t = M_tη′(t)` and the readout is `m = ∫₀¹ η′(t) dt`. Expanding the score gives coefficients
`η′(t) = (−aµ_t/c_t + c′_tµ_t²/(2c_t²) − c′_t/(2c_t), a/c_t − c′_tµ_t/c_t², c′_t/(2c_t²))`. (29)"

**Formalization Note.** `µ_t = bridgeMean a t`, `c_t = bridgeVar t`, `c′_t = deriv bridgeVar t`.
The time score is `∂_t log p_t(x)` (eq. (2)) of the Gaussian density `gaussianPDFReal µ_t c_t`
(variance `c_t` as an `ℝ≥0` via `Real.toNNReal`; `c_t ≥ 1/2 > 0` on `[0,1]`). The statement is for
`t ∈ [0, 1]`; `vCoef phi3 a t = M_t⁻¹b_t`, so its equality with `η′(t)` includes invertibility in
effect, and the readout is `m = ∫₀¹ η′(t) dt`. -/
theorem eq_26_29 (a : ℝ) :
    let μt : ℝ → ℝ := fun t => bridgeMean a t
    let ct : ℝ → ℝ := bridgeVar
    let dct : ℝ → ℝ := fun t => deriv bridgeVar t
    let ηp : ℝ → Fin 3 → ℝ := fun t =>
      ![-(a * μt t) / ct t + dct t * μt t ^ 2 / (2 * ct t ^ 2) - dct t / (2 * ct t),
        a / ct t - dct t * μt t / ct t ^ 2,
        dct t / (2 * ct t ^ 2)]
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      (pairLaw a).map (bridge t) = gaussianReal (μt t) (ct t).toNNReal) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ,
      deriv (fun s => Real.log (gaussianPDFReal (μt s) (ct s).toNNReal x)) t =
        a * (x - μt t) / ct t + dct t / (2 * ct t ^ 2) * ((x - μt t) ^ 2 - ct t)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ,
      a * (x - μt t) / ct t + dct t / (2 * ct t ^ 2) * ((x - μt t) ^ 2 - ct t) =
        phi3 x ⬝ᵥ ηp t) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, driftVec phi3 a t = momentMat phi3 a t *ᵥ ηp t) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, vCoef phi3 a t = ηp t) ∧
    readout phi3 a = fun i => ∫ t in (0 : ℝ)..1, ηp t i := by sorry

end LRTempElim
