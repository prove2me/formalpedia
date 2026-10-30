-- Prove2me | Theorems.Thm_FreedmanTail_eq_3_5_exp_moment_bound
-- name    : FreedmanTail.eq_3_5_exp_moment_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:10:09.648334+00:00
-- url     : https://prove2.me/theorems/cc8bccd7-ad52-47fc-b4b8-b7297236e095
-- title:
--   (3.5): $E\{\exp(\lambda X)\} \le 1 + e(\lambda)\operatorname{Var} X \le \exp[e(\lambda)\operatorname{Var} X]$
-- statement:
--   Let $X$ be a real random variable on a probability space with $X \le 1$ almost surely and $E(X) \le 0$, and let $\lambda \ge 0$. Then
--   $$E\{\exp(\lambda X)\} \le 1 + e(\lambda) \operatorname{Var} X \le \exp[e(\lambda) \operatorname{Var} X].$$
--   No integrability of $X$ is assumed and no lower bound on $X$: since $X \le 1$, $E(X) \in [-\infty, 1]$ always exists, and $\operatorname{Var} X \in [0, \infty]$.
--
--   This is the one-step estimate behind the supermartingale property of $Q_\lambda(T_n, S_n)$.
--
--   **Formalization Note** $E\{\exp(\lambda X)\}$ is a Lebesgue integral in $[0, \infty]$; $E(X) \le 0$ is $E(X^+) \le E(X^-)$; $\operatorname{Var} X$ is Mathlib's `evariance`, which equals $\infty$ when $X$ is not integrable (then $E(X^2) = \infty$). The second inequality is stated when $\operatorname{Var} X < \infty$.
--
--   Differences from the source:
--   - encoding: E(X) ≤ 0 for a random variable X ≤ 1 → ∫⁻ X⁺ ≤ ∫⁻ X⁻ (lower Lebesgue integrals), X a.e.-measurable; reason: X ≤ 1 makes E(X⁺) ≤ 1, so E(X) exists in [−∞, 1]; no integrability hypothesis is added
--   - encoding: random variable X with X ≤ 1 → Y AEMeasurable with Y ≤ 1 almost everywhere (h1); reason: every such Y agrees a.e. with a measurable Y′ ≤ 1 everywhere, and E{exp(λY)}, E(Y⁺), E(Y⁻) and Var Y are unchanged by a.e. modification, so the instances are the paper's up to null sets
--   - encoding: Var X → evariance X ∈ [0, ∞]; reason: Var X may be infinite; evariance is ∞ exactly when E(X²) = ∞, including when X is not integrable
--   - encoding: 1 + e(λ) Var X ≤ exp[e(λ) Var X] → stated under Var X ≠ ∞; reason: when Var X = ∞ both sides are +∞ (or 1 = 1 at λ = 0) and there is nothing to state
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975) 100–118, doi:10.1214/aop/1176996452, display (3.5), p. 106

import Mathlib
import Definitions.Def_FreedmanTail_eFun

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FreedmanTail

/-- **(3.5): `E{exp(λX)} ≤ 1 + e(λ) Var X ≤ exp[e(λ) Var X]` for `X ≤ 1`, `E(X) ≤ 0`.**
Freedman, *On Tail Probabilities for Martingales*, Ann. Probab. 3 (1975) 100–118, display (3.5),
p. 106: "E{exp(λX)} ≤ 1 + e(λ) Var X ≤ exp[e(λ) Var X] for λ ≥ 0 and random variables X
satisfying X ≤ 1 and E(X) ≤ 0."

Let `Y` be a real random variable on a probability space with `Y ≤ 1` a.s. and `E(Y) ≤ 0`, and let
`λ ≥ 0`. Then `E{exp(λY)} ≤ 1 + e(λ) Var Y`, and, when `Var Y < ∞`,
`1 + e(λ) Var Y ≤ exp[e(λ) Var Y]`.

**Formalization Note.** No integrability of `Y` is assumed. Since `Y ≤ 1`, `E(Y⁺) ≤ 1`, so
`E(Y) ∈ [−∞, 1]` always exists and "`E(Y) ≤ 0`" is `E(Y⁺) ≤ E(Y⁻)` (hypothesis `h0`, lower
Lebesgue integrals). `Var Y` is Mathlib's `evariance Y μ ∈ [0, ∞]`; its internal Bochner mean is
`0` when `Y` is not integrable, but then `E(Y²) = ∞` on a probability space and `evariance = ∞`,
the correct value. `E{exp(λY)}` is a lower Lebesgue integral in `[0, ∞]`. The second
inequality is stated where `Var Y < ∞`; where `Var Y = ∞` both of the paper's right-hand sides are
`+∞` and there is nothing to state. -/
theorem eq_3_5_exp_moment_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} {l : ℝ} (hY : AEMeasurable Y μ)
    (h1 : ∀ᵐ ω ∂μ, Y ω ≤ 1)
    (h0 : ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (- Y ω) ∂μ) (hl : 0 ≤ l) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * Y ω)) ∂μ ≤ 1 + ENNReal.ofReal (eFun l) * evariance Y μ
      ∧ (evariance Y μ ≠ ⊤ → 1 + ENNReal.ofReal (eFun l) * evariance Y μ
          ≤ ENNReal.ofReal (Real.exp (eFun l * (evariance Y μ).toReal))) := by sorry

end FreedmanTail
