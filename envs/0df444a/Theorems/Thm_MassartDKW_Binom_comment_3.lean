-- Prove2me | Theorems.Thm_MassartDKW_Binom_comment_3
-- name    : MassartDKW.Binom.comment_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:58:57.741621+00:00
-- url     : https://prove2.me/theorems/e9248a30-aadc-45dd-b578-4beae7222935
-- title:
--   Comment 3, p. 1273 — Cramér–Chernoff bound P(S − np > nε) ≤ exp(−n h(p, ε)) for S ~ Bin(n, p)
-- statement:
--   Let $S$ be a random variable with binomial distribution $\mathcal B(n,p)$, with $0 < p$, and set $q = 1 - p$. For every $\varepsilon$ with $0 < \varepsilon \le q$,
--
--   $$
--   P(S - np > n\varepsilon) \le \exp\bigl(-n\,h(p,\varepsilon)\bigr),
--   $$
--
--   where $h(p,\varepsilon) = (p+\varepsilon)\log\frac{p+\varepsilon}{p} + (q-\varepsilon)\log\frac{q-\varepsilon}{q}$ is the function of Lemma 1.
--
--   This is the classical Cramér–Chernoff bound for binomial tails (Massart cites Shorack and Wellner (1986), p. 440). With Lemma 1(ii) it gives Theorem 2 at once.
--
--   **Formalization Note.** $S$ is an $\mathbb N$-valued random variable on a probability space $(\Omega, P)$ whose law is Mathlib's `binomial n p` (the number of successes in $n$ independent trials with success probability $p \in [0,1]$); $n = 0$ is allowed. The hypothesis $p > 0$ is the standing assumption $q < 1$ of Lemma 1, under which $h$ is defined; at $p = 0$ Lean's $\log 0 = 0$ would make $h$ a junk value. The probability is an outer measure value in $[0,\infty]$, compared with the real bound through `ENNReal.ofReal`.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1273, Comment 3 (citing Shorack and Wellner 1986, p. 440)

import Mathlib
import Definitions.Def_MassartDKW_Binom_Setting

open MeasureTheory ProbabilityTheory

namespace MassartDKW.Binom

/-- Massart (1990), Comment 3, p. 1273 (Cramér–Chernoff bound): if `S` has the binomial law
`Bin(n, p)` with `0 < p` and `0 < ε ≤ q = 1 − p`, then `P(S − np > nε) ≤ exp(−n h(p, ε))`. -/
theorem comment_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (p : unitInterval) (S : Ω → ℕ) (hS : HasLaw S (binomial n p) P)
    (hp : 0 < (p : ℝ)) (ε : ℝ) (hε : 0 < ε) (hεq : ε ≤ 1 - (p : ℝ)) :
    P {ω | (n : ℝ) * ε < (S ω : ℝ) - n * (p : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) * h (p : ℝ) ε))) := by sorry

end MassartDKW.Binom
