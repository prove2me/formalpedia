-- Prove2me | Theorems.Thm_FreedmanTail_proof_3_3_supermartingale_step
-- name    : FreedmanTail.proof_3_3_supermartingale_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:11:30.373677+00:00
-- url     : https://prove2.me/theorems/ee2a7c95-6bf6-4784-9d50-7c04c4953f6e
-- title:
--   Proof of (3.3): $\{Q_\lambda(T_n, S_n), \mathcal F_n\}$ is expectation-decreasing
-- statement:
--   Setting (p. 101 and (3.4), p. 106): $(\Omega, \mathcal F, P)$ is a probability space, $\mathcal F_0 \subseteq \mathcal F_1 \subseteq \cdots$ are sub-$\sigma$-fields, and $X_1, X_2, \dots$ are real random variables with
--
--   1. $X_n$ $\mathcal F_n$-measurable;
--   2. $X_n \le 1$ almost surely;
--   3. $E\{X_n \mid \mathcal F_{n-1}\} \le 0$ almost surely,
--
--   for all $n \ge 1$. No integrability and no lower bound on $X_n$ are assumed. $V_n = \operatorname{Var}\{X_n \mid \mathcal F_{n-1}\} \in [0, \infty]$, $S_n = X_1 + \cdots + X_n$, $T_n = V_1 + \cdots + V_n$, $Q_\lambda(v, y) = \exp\{\lambda y - e(\lambda) v\}$.
--
--   Then for every $\lambda \ge 0$ and every $n \ge 0$, almost surely,
--   $$E\{Q_\lambda(T_{n+1}, S_{n+1}) \mid \mathcal F_n\} \le Q_\lambda(T_n, S_n),$$
--   that is, $\{Q_\lambda(T_n, S_n), \mathcal F_n\}$ is an expectation-decreasing martingale (a nonnegative supermartingale). This extends (1.4)(a) from bounded martingale differences to the one-sided condition (3.4).
--
--   **Formalization Note** Conditional expectations of the nonnegative process $Q_\lambda(T_n, S_n)$ are conditional Lebesgue expectations. $T_n \in [0, \infty]$ and $Q_\lambda(\infty, y) = 0$.
--
--   Differences from the source:
--   - encoding: increments X_1, X_2, …, X_n F_n-measurable, conditioned on F_{n−1} → X k is the paper's X_{k+1}, F (k+1)-measurable, conditioned on F k; reason: 0-based indexing of ℕ; same process
--   - encoding: E{X_n | F_{n−1}} ≤ 0 a.e., with no integrability assumed on X_n → E{X_n⁺ | F_{n−1}} ≤ E{X_n⁻ | F_{n−1}} a.e., with conditional Lebesgue expectations μ⁻[· | F k]; reason: X_n ≤ 1 makes E{X_n⁺ | F_{n−1}} finite, so the conditional mean exists in [−∞, 1] and this is exactly its sign condition; no integrability hypothesis is added
--   - encoding: V_n = Var{X_n | F_{n−1}}, T_n = V_1 + ⋯ + V_n → condVarE and varSum with values in [0, ∞]; T_n ≤ b is varSum ≤ ENNReal.ofReal b; reason: no integrability is assumed, so V_n may be infinite; where E{X_n² | F_{n−1}} < ∞ the value is the usual conditional variance, and T_n ≤ b is false where T_n = ∞
--   - encoding: Q_λ(v, y) = exp{λy − e(λ)v} → Qlam with value in [0, ∞), equal to 0 at v = ∞; reason: T_n may be infinite; 0 is the limit of exp{λy − e(λ)v} as v → ∞ for λ > 0, and a convention for λ = 0, where the paper's expression is exp{0 − 0·∞}
--   - encoding: {Q_λ(T_n, S_n), F_n} is an expectation-decreasing martingale → E{Q_λ(T_{k+1}, S_{k+1}) | F_k} ≤ Q_λ(T_k, S_k) a.e. for every k, with conditional Lebesgue expectations; reason: Q_λ(T_n, S_n) is nonnegative and F_n-measurable (T_{n+1} is F_n-measurable), so the one-step inequality is the supermartingale property
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975) 100–118, doi:10.1214/aop/1176996452, proof of (3.3), unnumbered, p. 106

import Mathlib
import Definitions.Def_FreedmanTail_Qlam
import Definitions.Def_FreedmanTail_partialSum
import Definitions.Def_FreedmanTail_varSum

open MeasureTheory
open scoped ENNReal

namespace FreedmanTail

/-- **`{Q_λ(T_n, S_n), F_n}` is expectation-decreasing.**
Freedman, *On Tail Probabilities for Martingales*, Ann. Probab. 3 (1975) 100–118, proof of (3.3),
unnumbered, p. 106: "It is enough to show that {Q_λ{T_n, S_n}, F_n} is an expectation-decreasing
martingale."

Assume (p. 101 and (3.4), p. 106) that every `X k` (the paper's `X_{k+1}`) is
`F (k+1)`-measurable, `X k ≤ 1` a.e. and `E{X k | F k} ≤ 0` a.e. Then for every `λ ≥ 0` and
every `k`, a.e.,
`E{Q_λ(T_{k+1}, S_{k+1}) | F_k} ≤ Q_λ(T_k, S_k)`.

**Formalization Note.** The supermartingale property is stated with the conditional Lebesgue
expectation `μ⁻[· | F k]` of the nonnegative process `Q_λ(T_n, S_n) ∈ [0, ∞)`, which needs no
integrability argument. `T_n ∈ [0, ∞]` and `Q_λ(∞, y) = 0` (see `Qlam`). The conditional mean
condition is `E{(X k)⁺ | F k} ≤ E{(X k)⁻ | F k}` a.e.; no integrability of `X k` is assumed. -/
theorem proof_3_3_supermartingale_step {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable[F (k + 1)] (X k))
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ 1)
    (hdrift : ∀ k, μ⁻[fun ω => ENNReal.ofReal (X k ω) | F k]
      ≤ᵐ[μ] μ⁻[fun ω => ENNReal.ofReal (- X k ω) | F k])
    {l : ℝ} (hl : 0 ≤ l) (k : ℕ) :
    μ⁻[fun ω => Qlam l (varSum F μ X (k + 1) ω) (partialSum X (k + 1) ω) | F k]
      ≤ᵐ[μ] fun ω => Qlam l (varSum F μ X k ω) (partialSum X k ω) := by sorry

end FreedmanTail
