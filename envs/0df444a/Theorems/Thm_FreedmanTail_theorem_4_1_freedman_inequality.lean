-- Prove2me | Theorems.Thm_FreedmanTail_theorem_4_1_freedman_inequality
-- name    : FreedmanTail.theorem_4_1_freedman_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:13:33.677989+00:00
-- url     : https://prove2.me/theorems/1653a750-550a-4bdb-9921-acdd370ec5e0
-- title:
--   (4.1) Theorem: Freedman's inequality
-- statement:
--   Setting (p. 101 and (3.4), p. 106): $(\Omega, \mathcal F, P)$ is a probability space, $\mathcal F_0 \subseteq \mathcal F_1 \subseteq \cdots$ are sub-$\sigma$-fields, and $X_1, X_2, \dots$ are real random variables with
--
--   1. $X_n$ $\mathcal F_n$-measurable;
--   2. $X_n \le 1$ almost surely;
--   3. $E\{X_n \mid \mathcal F_{n-1}\} \le 0$ almost surely,
--
--   for all $n \ge 1$. No integrability and no lower bound on $X_n$ are assumed. $V_n = \operatorname{Var}\{X_n \mid \mathcal F_{n-1}\} \in [0, \infty]$, $S_n = X_1 + \cdots + X_n$, $T_n = V_1 + \cdots + V_n$, $Q_\lambda(v, y) = \exp\{\lambda y - e(\lambda) v\}$.
--
--   Then for any positive numbers $a$ and $b$,
--   $$P\{S_n \ge a \text{ and } T_n \le b \text{ for some } n = 1, 2, \dots\} \le \Big(\frac{b}{a+b}\Big)^{a+b} e^{a} \le \exp\Big[-\frac{a^2}{2(a+b)}\Big].$$
--
--   This is Freedman's inequality: a Bernstein-type bound for sums of supermartingale differences bounded above by $1$, in which the number of terms is replaced by the accumulated conditional variance $T_n$ and the bound is uniform over all times $n$. It contains Bernstein's inequality for independent summands and is the tool behind the law of the iterated logarithm for martingales in §6.
--
--   **Formalization Note** Lean's `X k` is the paper's $X_{k+1}$; $\mathcal F_0$ is arbitrary. Conditional expectations are conditional Lebesgue expectations of nonnegative functions, so no integrability hypothesis appears; $T_n$ takes values in $[0, \infty]$ and "$T_n \le b$" fails where $T_n = \infty$. The power $(b/(a+b))^{a+b}$ is the real power.
--
--   Differences from the source:
--   - encoding: increments X_1, X_2, …, X_n F_n-measurable, conditioned on F_{n−1} → X k is the paper's X_{k+1}, F (k+1)-measurable, conditioned on F k; reason: 0-based indexing of ℕ; same process
--   - encoding: E{X_n | F_{n−1}} ≤ 0 a.e., with no integrability assumed on X_n → E{X_n⁺ | F_{n−1}} ≤ E{X_n⁻ | F_{n−1}} a.e., with conditional Lebesgue expectations μ⁻[· | F k]; reason: X_n ≤ 1 makes E{X_n⁺ | F_{n−1}} finite, so the conditional mean exists in [−∞, 1] and this is exactly its sign condition; no integrability hypothesis is added
--   - encoding: V_n = Var{X_n | F_{n−1}}, T_n = V_1 + ⋯ + V_n → condVarE and varSum with values in [0, ∞]; T_n ≤ b is varSum ≤ ENNReal.ofReal b; reason: no integrability is assumed, so V_n may be infinite; where E{X_n² | F_{n−1}} < ∞ the value is the usual conditional variance, and T_n ≤ b is false where T_n = ∞
--   - encoding: for some n = 1, 2, ··· → ∃ n : ℕ; reason: n = 0 adds nothing because S_0 = 0 < a
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975) 100–118, doi:10.1214/aop/1176996452, (4.1) Theorem, p. 107; hypothesis (3.4), p. 106; setup and (1.2), p. 101

import Mathlib
import Definitions.Def_FreedmanTail_partialSum
import Definitions.Def_FreedmanTail_varSum

open MeasureTheory
open scoped ENNReal

namespace FreedmanTail

/-- **(4.1) Theorem (Freedman's inequality).**
Freedman, *On Tail Probabilities for Martingales*, Ann. Probab. 3 (1975) 100–118,
(4.1) Theorem, p. 107: "Suppose (3.4). For any positive numbers a and b,
P{S_n ≥ a and T_n ≤ b for some n = 1, 2, ···} ≤ (b/(a + b))^(a+b) e^a ≤ exp[−a²/(2(a + b))]."

Setting (p. 101): `(Ω, F, P)` a probability space, `F_0 ⊂ F_1 ⊂ ⋯` sub-σ-fields, `X_n`
`F_n`-measurable, `V_n = Var{X_n | F_{n−1}}`, `S_n = X_1 + ⋯ + X_n`, `T_n = V_1 + ⋯ + V_n`.
(3.4), p. 106: `X_n ≤ 1` a.e. and `E{X_n | F_{n−1}} ≤ 0` a.e. for all `n`; no lower bound on
`X_n`.

**Formalization Note.** Index shift: Lean `X k` is the paper's `X_{k+1}`; it is
`F (k+1)`-measurable and conditioned on `F k`; `F 0` is arbitrary. No integrability of `X k` is
assumed: `X k ≤ 1` makes `E{(X k)⁺ | F k}` finite, so the conditional mean exists in `[−∞, 1]`
and "`≤ 0`" is `E{(X k)⁺ | F k} ≤ E{(X k)⁻ | F k}` a.e. (conditional Lebesgue expectations
`μ⁻[· | F k]`). The conditional variances, hence `T_n`, take values in `[0, ∞]` (`condVarE`,
`varSum`); "`T_n ≤ b`" is false where `T_n = ∞`. `n` ranges over `ℕ` (`n = 0` adds nothing since
`S_0 = 0 < a`). `(b/(a+b))^(a+b)` is the real power `Real.rpow`. -/
theorem theorem_4_1_freedman_inequality {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable[F (k + 1)] (X k))
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ 1)
    (hdrift : ∀ k, μ⁻[fun ω => ENNReal.ofReal (X k ω) | F k]
      ≤ᵐ[μ] μ⁻[fun ω => ENNReal.ofReal (- X k ω) | F k])
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    μ {ω | ∃ n, a ≤ partialSum X n ω ∧ varSum F μ X n ω ≤ ENNReal.ofReal b}
        ≤ ENNReal.ofReal ((b / (a + b)) ^ (a + b) * Real.exp a)
      ∧ (b / (a + b)) ^ (a + b) * Real.exp a ≤ Real.exp (-(a ^ 2) / (2 * (a + b))) := by sorry

end FreedmanTail
