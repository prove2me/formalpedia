-- Prove2me | Theorems.Thm_MassartDKW_Binom_theorem_2
-- name    : MassartDKW.Binom.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:58:43.931923+00:00
-- url     : https://prove2.me/theorems/598dfaf5-8234-46e8-bc9a-5743aeda5328
-- title:
--   Theorem 2, p. 1271 — P(S − np > nε) ≤ exp(−nε²/(2(p + ε/3)(q − ε/3))) for S ~ Bin(n, p), 0 < ε ≤ q
-- statement:
--   Let $S$ be a random variable with binomial distribution $\mathcal B(n,p)$ and set $q = 1 - p$. Then for every $\varepsilon$ with $0 < \varepsilon \le q$,
--
--   $$
--   P(S - np > n\varepsilon) \;\le\; \exp\!\left(-\frac{n\varepsilon^2}{2\,(p + \varepsilon/3)(q - \varepsilon/3)}\right).
--   $$
--
--   Massart obtains this exponential bound for binomial upper tails as a by-product of his proof of the tight Dvoretzky–Kiefer–Wolfowitz inequality. The factor $(q - \varepsilon/3)$ in the denominator makes it sharper than Bernstein's inequality, whose denominator is $2(pq + \varepsilon/3)$, and it also implies Hoeffding's bound $\exp(-2n\varepsilon^2)$.
--
--   **Formalization Note.** $S$ is an $\mathbb N$-valued random variable on a probability space $(\Omega,P)$ whose law is Mathlib's `binomial n p`, with $p \in [0,1]$; $n = 0$ and $p = 0$ are allowed, as on the page. The denominator is positive on the whole range, since $q - \varepsilon/3 \ge 2q/3 > 0$. The event is the strict upper tail $S - np > n\varepsilon$, and its probability, an element of $[0,\infty]$, is compared with the real bound through `ENNReal.ofReal`.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1271, Theorem 2

import Mathlib
import Definitions.Def_MassartDKW_Binom_Setting

open MeasureTheory ProbabilityTheory

namespace MassartDKW.Binom

/-- Massart (1990), Theorem 2, p. 1271: if `S` has the binomial law `Bin(n, p)` and `q = 1 − p`,
then for every `ε` with `0 < ε ≤ q`,
`P(S − np > nε) ≤ exp(−nε²/(2(p + ε/3)(q − ε/3)))`. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (p : unitInterval) (S : Ω → ℕ) (hS : HasLaw S (binomial n p) P)
    (ε : ℝ) (hε : 0 < ε) (hεq : ε ≤ 1 - (p : ℝ)) :
    P {ω | (n : ℝ) * ε < (S ω : ℝ) - n * (p : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) * ε ^ 2) /
        (2 * ((p : ℝ) + ε / 3) * (1 - (p : ℝ) - ε / 3)))) := by sorry

end MassartDKW.Binom
