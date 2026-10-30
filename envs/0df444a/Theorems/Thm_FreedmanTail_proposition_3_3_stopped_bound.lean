-- Prove2me | Theorems.Thm_FreedmanTail_proposition_3_3_stopped_bound
-- name    : FreedmanTail.proposition_3_3_stopped_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:12:06.730023+00:00
-- url     : https://prove2.me/theorems/69658d8f-0683-48f7-ad4b-f67d9ad3a074
-- title:
--   (3.3) Proposition: $\int_{\{\sigma<\infty\}} Q_\lambda(T_\sigma, S_\sigma)\,dP \le 1$ for any stopping time
-- statement:
--   Setting (p. 101 and (3.4), p. 106): $(\Omega, \mathcal F, P)$ is a probability space, $\mathcal F_0 \subseteq \mathcal F_1 \subseteq \cdots$ are sub-$\sigma$-fields, and $X_1, X_2, \dots$ are real random variables with
--
--   1. $X_n$ $\mathcal F_n$-measurable;
--   2. $X_n \le 1$ almost surely;
--   3. $E\{X_n \mid \mathcal F_{n-1}\} \le 0$ almost surely,
--
--   for all $n \ge 1$. No integrability and no lower bound on $X_n$ are assumed. $V_n = \operatorname{Var}\{X_n \mid \mathcal F_{n-1}\} \in [0, \infty]$, $S_n = X_1 + \cdots + X_n$, $T_n = V_1 + \cdots + V_n$, $Q_\lambda(v, y) = \exp\{\lambda y - e(\lambda) v\}$.
--
--   Then for every $\lambda \ge 0$ and every stopping time $\sigma$ (values in $\{0, 1, 2, \dots, \infty\}$, $\{\sigma = n\} \in \mathcal F_n$, $P\{\sigma = \infty\} > 0$ allowed),
--   $$\int_{\{\sigma < \infty\}} Q_\lambda(T_\sigma, S_\sigma)\, dP \le 1 .$$
--   The stopping time need not be bounded. This is the optional-stopping bound from which (4.1) follows by choosing $\sigma$ as the first passage of $S_n$ above $a$.
--
--   **Formalization Note** A stopping time is Mathlib's `IsStoppingTime F σ` with values in `WithTop ℕ` ($\top$ is $\infty$); on $\{\sigma < \infty\}$ the stopped values use the natural number $\sigma(\omega)$.
--
--   Differences from the source:
--   - encoding: increments X_1, X_2, …, X_n F_n-measurable, conditioned on F_{n−1} → X k is the paper's X_{k+1}, F (k+1)-measurable, conditioned on F k; reason: 0-based indexing of ℕ; same process
--   - encoding: E{X_n | F_{n−1}} ≤ 0 a.e., with no integrability assumed on X_n → E{X_n⁺ | F_{n−1}} ≤ E{X_n⁻ | F_{n−1}} a.e., with conditional Lebesgue expectations μ⁻[· | F k]; reason: X_n ≤ 1 makes E{X_n⁺ | F_{n−1}} finite, so the conditional mean exists in [−∞, 1] and this is exactly its sign condition; no integrability hypothesis is added
--   - encoding: V_n = Var{X_n | F_{n−1}}, T_n = V_1 + ⋯ + V_n → condVarE and varSum with values in [0, ∞]; T_n ≤ b is varSum ≤ ENNReal.ofReal b; reason: no integrability is assumed, so V_n may be infinite; where E{X_n² | F_{n−1}} < ∞ the value is the usual conditional variance, and T_n ≤ b is false where T_n = ∞
--   - encoding: Q_λ(v, y) = exp{λy − e(λ)v} → Qlam with value in [0, ∞), equal to 0 at v = ∞; reason: T_n may be infinite; 0 is the limit of exp{λy − e(λ)v} as v → ∞ for λ > 0, and a convention for λ = 0, where the paper's expression is exp{0 − 0·∞}
--   - encoding: stopping time: {τ = n} ∈ F_n for n = 0, 1, 2, ···, values in {0, 1, 2, ···, ∞} → IsStoppingTime F σ with σ : Ω → WithTop ℕ ({σ ≤ n} ∈ F n), ⊤ = ∞; reason: over ℕ the two conditions are equivalent
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975) 100–118, doi:10.1214/aop/1176996452, (3.3) Proposition and (3.4), p. 106

import Mathlib
import Definitions.Def_FreedmanTail_Qlam
import Definitions.Def_FreedmanTail_partialSum
import Definitions.Def_FreedmanTail_varSum

open MeasureTheory
open scoped ENNReal

namespace FreedmanTail

/-- **(3.3) Proposition: `∫_{σ<∞} Q_λ(T_σ, S_σ) dP ≤ 1` for any stopping time `σ`.**
Freedman, *On Tail Probabilities for Martingales*, Ann. Probab. 3 (1975) 100–118,
(3.3) Proposition, p. 106: "∫_{σ<∞} Q_λ(T_σ, S_σ) dP ≤ 1 for λ ≥ 0 and any stopping time σ,
provided (3.4) X_n ≤ 1 a.e. and E{X_n | F_{n−1}} ≤ 0 a.e. for all n."

Setting (p. 101): `X k` (the paper's `X_{k+1}`) is `F (k+1)`-measurable; (3.4): `X k ≤ 1` a.e.
and `E{X k | F k} ≤ 0` a.e. for all `k`. For every `λ ≥ 0` and every stopping time `σ` (taking
values in `{0, 1, 2, …, ∞}`, `P{σ = ∞} > 0` allowed),
`∫_{σ<∞} Q_λ(T_σ, S_σ) dP ≤ 1`.

**Formalization Note.** A stopping time is Mathlib's `IsStoppingTime F σ` with
`σ : Ω → WithTop ℕ` (`{σ ≤ n} ∈ F n`, equivalent over `ℕ` to the paper's `{σ = n} ∈ F_n`); `⊤`
is the value `∞`. On `{σ ≠ ⊤}` the stopped values use `(σ ω).untopA`, the natural number `σ ω`.
The stopping time is arbitrary (not bounded). The conditional mean condition is
`E{(X k)⁺ | F k} ≤ E{(X k)⁻ | F k}` a.e.; no integrability of `X k` is assumed. -/
theorem proposition_3_3_stopped_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable[F (k + 1)] (X k))
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ 1)
    (hdrift : ∀ k, μ⁻[fun ω => ENNReal.ofReal (X k ω) | F k]
      ≤ᵐ[μ] μ⁻[fun ω => ENNReal.ofReal (- X k ω) | F k])
    {l : ℝ} (hl : 0 ≤ l) (σ : Ω → WithTop ℕ) (hσ : IsStoppingTime F σ) :
    ∫⁻ ω in {ω | σ ω ≠ ⊤},
        Qlam l (varSum F μ X (σ ω).untopA ω) (partialSum X (σ ω).untopA ω) ∂μ ≤ 1 := by sorry

end FreedmanTail
