-- Prove2me | Theorems.Thm_OnlineCarpoolingLei_Oblivious_cube_root_discrepancy
-- name    : OnlineCarpoolingLei.Oblivious.cube_root_discrepancy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:51.391799+00:00
-- url     : https://prove2.me/theorems/d9e64b4e-e559-4149-846f-d67cb85e6d9d
-- title:
--   Theorem 1.2 — online carpooling with $\mathbb P(M_T\ge D)\le12T\exp[-(D/40)^3]$ against an oblivious adversary
-- statement:
--   Let $n\ge2$. Edges $e_t=\mathbf 1_{u_t}-\mathbf 1_{v_t}$ with $u_t\ne v_t$ in $[n]$ arrive one at a time; an online algorithm chooses $\varepsilon_t\in\{-1,+1\}$ immediately, seeing only $e_1,\dots,e_t$ and its own randomness, and the discrepancy evolves by $d_0=0$, $d_t=d_{t-1}+\varepsilon_te_t$. Let $M_T=\max_{0\le t\le T}\|d_t\|_\infty$.
--
--   **Theorem.** For every $n\ge2$ there is a randomized online algorithm, independent of $T$, such that for every sequence of $T\ge1$ edges on $[n]$ fixed in advance and every integer $D\ge300$,
--   $$\mathbb P(M_T\ge D)\le12T\exp\Big[-\Big(\frac D{40}\Big)^3\Big].\tag{1.3}$$
--   Consequently, for every $c\ge0$, with probability at least $1-e^{-c}$,
--   $$M_T<\max\Big\{300,\;40\big(c+\log(12T)\big)^{1/3}\Big\}.\tag{1.4}$$
--
--   Here $\log$ is the natural logarithm. One algorithm is chosen for each $n$ and serves every horizon $T$, every input and every $D$, $c$; the constants $12$, $40$, $300$ do not depend on $n$ or $T$. This gives $M_T=O((\log T)^{1/3})$ with high probability on every oblivious input, resolving Conjecture 2 of Kulkarni, Reis and Rothvoss and matching the known lower bound.
--
--   Differences from the source:
--   - encoding: vertex set $[n]$ and a sequence of $T$ edges → `Fin n` and the first $T$ entries of `E : ℕ → Edge n` (`E t` $=e_{t+1}$); reason: every finite sequence extends to an infinite one, and the rule reads only revealed prefixes, so the run up to $T$ does not depend on the extension
--   - encoding: randomized online algorithm → `OnlineAlgorithm n`, a rule whose step $t$ reads the first $t$ edges and the first $t$ values of a tape of independent uniform $[0,1)$ variables, measurable in the tape, with the bounds required on every probability space carrying such a tape; reason: binary randomized decisions on finite histories can be sampled from independent uniforms; the algorithm of Section 3 uses precisely this realization, and transporting its tape law to another probability space changes no finite-prefix law
--   - encoding: integer $D\ge300$ → `D : ℕ` with `300 ≤ D`; reason: same set of values
--   - encoding: probabilities → measures in $[0,\infty]$, with the real bounds embedded by `ENNReal.ofReal`; reason: both bounds are nonnegative ($1-e^{-c}\ge0$ for $c\ge0$), so the embedding is exact
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Theorem 1.2, (1.3)–(1.4), p.3 (PDF p.3); model (1.1)–(1.2) on p.2; proof on p.9

import Mathlib
import Definitions.Def_OnlineCarpoolingLei_Oblivious_Model

open MeasureTheory ProbabilityTheory

namespace OnlineCarpoolingLei.Oblivious

/-- Theorem 1.2 (p.3). For every `n ≥ 2` there is a randomized online algorithm, independent of
`T`, such that for every sequence of `T ≥ 1` edges on `[n]` fixed in advance and every integer
`D ≥ 300`, (1.3) `P(M_T ≥ D) ≤ 12T exp[−(D/40)³]`; and for every `c ≥ 0`, with probability at
least `1 − e^{−c}`, (1.4) `M_T < max {300, 40 (c + log(12T))^{1/3}}`.
The rule is chosen before the probability space, the input, the horizon, `D` and `c`. -/
theorem cube_root_discrepancy (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : OnlineAlgorithm n, A.IsMeasurable ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (U : ℕ → Ω → ℝ), IsUniformTape P U →
        ∀ (E : ℕ → Edge n) (T : ℕ), 1 ≤ T →
          (∀ D : ℕ, 300 ≤ D →
            P {ω | D ≤ maxDisc (A.disc E fun t => U t ω) T} ≤
              ENNReal.ofReal (12 * T * Real.exp (-((D : ℝ) / 40) ^ 3))) ∧
          (∀ c : ℝ, 0 ≤ c →
            ENNReal.ofReal (1 - Real.exp (-c)) ≤
              P {ω | ((maxDisc (A.disc E fun t => U t ω) T : ℕ) : ℝ) <
                max 300 (40 * (c + Real.log (12 * T)) ^ ((1 : ℝ) / 3))}) := by sorry

end OnlineCarpoolingLei.Oblivious
