-- Prove2me | Theorems.Thm_FreedmanTail_proof_4_1_lambda_bound
-- name    : FreedmanTail.proof_4_1_lambda_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:12:47.243464+00:00
-- url     : https://prove2.me/theorems/ad14588b-bf70-401c-882c-c555f0227fa6
-- title:
--   Proof of (4.1): $P\{S_n \ge a,\ T_n \le b \text{ for some } n\} \le \exp[-\lambda a + e(\lambda) b]$
-- statement:
--   Setting (p. 101 and (3.4), p. 106): $(\Omega, \mathcal F, P)$ is a probability space, $\mathcal F_0 \subseteq \mathcal F_1 \subseteq \cdots$ are sub-$\sigma$-fields, and $X_1, X_2, \dots$ are real random variables with
--
--   1. $X_n$ $\mathcal F_n$-measurable;
--   2. $X_n \le 1$ almost surely;
--   3. $E\{X_n \mid \mathcal F_{n-1}\} \le 0$ almost surely,
--
--   for all $n \ge 1$. No integrability and no lower bound on $X_n$ are assumed. $V_n = \operatorname{Var}\{X_n \mid \mathcal F_{n-1}\} \in [0, \infty]$, $S_n = X_1 + \cdots + X_n$, $T_n = V_1 + \cdots + V_n$, $Q_\lambda(v, y) = \exp\{\lambda y - e(\lambda) v\}$.
--
--   Then for all $a > 0$, $b > 0$ and $\lambda \ge 0$,
--   $$P\{S_n \ge a \text{ and } T_n \le b \text{ for some } n\} \le \exp[-\lambda a + e(\lambda) b].$$
--   Optimising over $\lambda$ (the minimiser is $\lambda = \log[(a+b)/b]$) gives the first bound of (4.1).
--
--   Differences from the source:
--   - encoding: increments X_1, X_2, …, X_n F_n-measurable, conditioned on F_{n−1} → X k is the paper's X_{k+1}, F (k+1)-measurable, conditioned on F k; reason: 0-based indexing of ℕ; same process
--   - encoding: E{X_n | F_{n−1}} ≤ 0 a.e., with no integrability assumed on X_n → E{X_n⁺ | F_{n−1}} ≤ E{X_n⁻ | F_{n−1}} a.e., with conditional Lebesgue expectations μ⁻[· | F k]; reason: X_n ≤ 1 makes E{X_n⁺ | F_{n−1}} finite, so the conditional mean exists in [−∞, 1] and this is exactly its sign condition; no integrability hypothesis is added
--   - encoding: V_n = Var{X_n | F_{n−1}}, T_n = V_1 + ⋯ + V_n → condVarE and varSum with values in [0, ∞]; T_n ≤ b is varSum ≤ ENNReal.ofReal b; reason: no integrability is assumed, so V_n may be infinite; where E{X_n² | F_{n−1}} < ∞ the value is the usual conditional variance, and T_n ≤ b is false where T_n = ∞
--   - encoding: A = {S_n ≥ a and T_n ≤ b for some n} → ∃ n : ℕ (including n = 0); reason: n = 0 adds nothing because S_0 = 0 < a
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975) 100–118, doi:10.1214/aop/1176996452, proof of (4.1), unnumbered, pp. 107–108

import Mathlib
import Definitions.Def_FreedmanTail_eFun
import Definitions.Def_FreedmanTail_partialSum
import Definitions.Def_FreedmanTail_varSum

open MeasureTheory
open scoped ENNReal

namespace FreedmanTail

/-- **The one-parameter bound `P{A} ≤ exp[−λa + e(λ)b]` in the proof of (4.1).**
Freedman, *On Tail Probabilities for Martingales*, Ann. Probab. 3 (1975) 100–118, proof of (4.1),
unnumbered, pp. 107–108: "Let A = {S_n ≥ a and T_n ≤ b for some n}. … Use (3.3)
1 ≥ ∫_A exp[λS_σ − e(λ)T_σ] dP ≥ P{A} · exp[λa − e(λ)b], so P{A} ≤ exp[−λa + e(λ)b]."

Under the setting of p. 101 (`X k`, the paper's `X_{k+1}`, is `F (k+1)`-measurable) and (3.4)
(`X k ≤ 1` a.e., `E{X k | F k} ≤ 0` a.e.), for all `a > 0`, `b > 0` and `λ ≥ 0`,
`P{S_n ≥ a and T_n ≤ b for some n} ≤ exp[−λa + e(λ)b]`.

**Formalization Note.** `n` ranges over all of `ℕ`; `n = 0` adds nothing because `S_0 = 0 < a`.
`T_n ∈ [0, ∞]`, and "`T_n ≤ b`" is `T_n ≤ ENNReal.ofReal b`, false where `T_n = ∞`. The
conditional mean condition is `E{(X k)⁺ | F k} ≤ E{(X k)⁻ | F k}` a.e.; no integrability of
`X k` is assumed. -/
theorem proof_4_1_lambda_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable[F (k + 1)] (X k))
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ 1)
    (hdrift : ∀ k, μ⁻[fun ω => ENNReal.ofReal (X k ω) | F k]
      ≤ᵐ[μ] μ⁻[fun ω => ENNReal.ofReal (- X k ω) | F k])
    {a b l : ℝ} (ha : 0 < a) (hb : 0 < b) (hl : 0 ≤ l) :
    μ {ω | ∃ n, a ≤ partialSum X n ω ∧ varSum F μ X n ω ≤ ENNReal.ofReal b}
      ≤ ENNReal.ofReal (Real.exp (-(l * a) + eFun l * b)) := by sorry

end FreedmanTail
