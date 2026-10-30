-- Prove2me | Theorems.Thm_FreedmanTail_proof_3_3_conditional_exp_bound
-- name    : FreedmanTail.proof_3_3_conditional_exp_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:10:41.540075+00:00
-- url     : https://prove2.me/theorems/aafed970-2580-4212-9fe7-6154ae65aee6
-- title:
--   Proof of (3.3): conditional form of (3.5), $E\{e^{\lambda X_n} \mid \mathcal F_{n-1}\} \le 1 + e(\lambda) V_n$
-- statement:
--   Let $\mathcal F_{n-1} \subseteq \mathcal F_n$ be sub-$\sigma$-fields of a probability space and $X_n$ a real $\mathcal F_n$-measurable random variable with $X_n \le 1$ almost surely and $E\{X_n \mid \mathcal F_{n-1}\} \le 0$ almost surely; no integrability is assumed. Then for every $\lambda \ge 0$, almost surely,
--   $$E\{\exp(\lambda X_n) \mid \mathcal F_{n-1}\} \le 1 + e(\lambda) V_n , \qquad V_n = \operatorname{Var}\{X_n \mid \mathcal F_{n-1}\} \in [0, \infty].$$
--   This is (3.5) applied to the conditional law of $X_n$ given $\mathcal F_{n-1}$, the step the proof of (3.3) uses.
--
--   **Formalization Note** Lean's `X k` is the paper's $X_{k+1}$ and `F k` the paper's $\mathcal F_k$. Conditional expectations are conditional Lebesgue expectations of nonnegative functions; $E\{X_n \mid \mathcal F_{n-1}\} \le 0$ is $E\{X_n^+ \mid \mathcal F_{n-1}\} \le E\{X_n^- \mid \mathcal F_{n-1}\}$.
--
--   Differences from the source:
--   - encoding: increments X_1, X_2, …, X_n F_n-measurable, conditioned on F_{n−1} → X k is the paper's X_{k+1}, F (k+1)-measurable, conditioned on F k; reason: 0-based indexing of ℕ; same process
--   - encoding: E{X_n | F_{n−1}} ≤ 0 a.e., with no integrability assumed on X_n → E{X_n⁺ | F_{n−1}} ≤ E{X_n⁻ | F_{n−1}} a.e., with conditional Lebesgue expectations μ⁻[· | F k]; reason: X_n ≤ 1 makes E{X_n⁺ | F_{n−1}} finite, so the conditional mean exists in [−∞, 1] and this is exactly its sign condition; no integrability hypothesis is added
--   - encoding: V_n = Var{X_n | F_{n−1}} → condVarE (F k) μ (X k) ∈ [0, ∞]; reason: no integrability is assumed, so V_n may be infinite
--   - reading: "This follows from (3.5)" (unconditional (3.5) applied inside the proof of (3.3)) → (3.5) stated for conditional expectations given F_{n−1}; reason: the proof applies (3.5) to the conditional distribution of X_n given F_{n−1}; this is that application
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975) 100–118, doi:10.1214/aop/1176996452, proof of (3.3), unnumbered, p. 106 (application of (3.5) to the conditional law of X_n given F_{n−1})

import Mathlib
import Definitions.Def_FreedmanTail_eFun
import Definitions.Def_FreedmanTail_condVarE

open MeasureTheory
open scoped ENNReal

namespace FreedmanTail

/-- **(3.5) in conditional form: `E{exp(λX_n) | F_{n−1}} ≤ 1 + e(λ) V_n`.**
Freedman, *On Tail Probabilities for Martingales*, Ann. Probab. 3 (1975) 100–118, proof of (3.3),
unnumbered, p. 106: "It is enough to show that {Q_λ{T_n, S_n}, F_n} is an expectation-decreasing
martingale. This follows from (3.5)", where (3.5) is applied to the conditional law of `X_n` given
`F_{n−1}`.

Setting (p. 101 and (3.4), p. 106): `F` is a filtration, `X k` (the paper's `X_{k+1}`) is
`F (k+1)`-measurable, `X k ≤ 1` a.e., and `E{X k | F k} ≤ 0` a.e. Then for every `λ ≥ 0`, a.e.,
`E{exp(λ X k) | F k} ≤ 1 + e(λ) Var{X k | F k}`.

**Formalization Note.** Index shift: Lean `X k` is the paper's `X_{k+1}`, `F k` the paper's
`F_k`. No integrability of `X k` is assumed: the conditional mean condition is
`E{(X k)⁺ | F k} ≤ E{(X k)⁻ | F k}` a.e. with conditional Lebesgue expectations `μ⁻[· | F k]`,
and the conditional variance is `condVarE ∈ [0, ∞]`. In `ℝ≥0∞`, `0 · ∞ = 0`. -/
theorem proof_3_3_conditional_exp_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (k : ℕ) {l : ℝ}
    (hXk : Measurable[F (k + 1)] (X k))
    (hlek : ∀ᵐ ω ∂μ, X k ω ≤ 1)
    (hdriftk : μ⁻[fun ω => ENNReal.ofReal (X k ω) | F k]
      ≤ᵐ[μ] μ⁻[fun ω => ENNReal.ofReal (- X k ω) | F k])
    (hl : 0 ≤ l) :
    μ⁻[fun ω => ENNReal.ofReal (Real.exp (l * X k ω)) | F k]
      ≤ᵐ[μ] fun ω => 1 + ENNReal.ofReal (eFun l) * condVarE (F k) μ (X k) ω := by sorry

end FreedmanTail
