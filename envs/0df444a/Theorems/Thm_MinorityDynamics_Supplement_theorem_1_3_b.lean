-- Prove2me | Theorems.Thm_MinorityDynamics_Supplement_theorem_1_3_b
-- name    : MinorityDynamics.Supplement.theorem_1_3_b
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:04:07.526212+00:00
-- url     : https://prove2.me/theorems/aaa34e91-80f9-4c13-a122-faf3a058b757
-- title:
--   Theorem 1.3(b) — for $17\le k\le\frac{1-\varepsilon}{\ln(5/4)}\ln n$, some source-free configuration needs $e^{\Omega(n^\varepsilon/k)}$ rounds w.h.p.
-- statement:
--   In $k$-Minority each of $n$ agents holds one of two opinions; in each synchronous round every non-source agent samples $k$ agents uniformly with replacement (itself and any sources included), independently, and adopts the less frequent opinion present in its sample (a unanimous sample is adopted); sources never change their opinion. The **consensus time** $\tau_0$ is the first round $t\ge0$ at which all agents hold the same opinion. Throughout, $n$ and $k$ are odd and $\ln$ is the natural logarithm.
--
--   There are absolute constants $c,c'>0$ such that, for every fixed $\varepsilon\in(0,1)$ and all sufficiently large $n$ (depending on $\varepsilon$): if
--
--   $$17\le k\le \frac{1-\varepsilon}{\ln(5/4)}\,\ln n,$$
--
--   then there is an initial configuration without sources from which, with probability at least $1-n^{-c'}$,
--
--   $$\tau_0 \;>\; \Big\lfloor \exp\Big(\frac{c\,n^{\varepsilon}}{k}\Big)\Big\rfloor .$$
--
--   Below the logarithmic threshold $\log_{5/4} n$, even source-free consensus can take superpolynomially many rounds: a sample-size barrier for $k$-Minority without sources.
--
--   **Formalization Note** The dynamics is `agentStep n k ∅`; $n^{\varepsilon}$ is the real power. The constants $c,c'$ do not depend on $\varepsilon$; only the threshold $N$ does. No condition $k\ge 8\ln n$ is imposed.
--
--   Differences from the source:
--   - encoding: 17 ≤ k ≤ ((1−ε)/ln(5/4)) ln n for a fixed ε ∈ (0,1); n, k odd; for sufficiently large n (p.2) → ∀ ε ∈ (0,1), ∃ N such that the claim holds for every odd n ≥ N and odd k with 17 ≤ k and k ≤ (1 − ε)/ln(5/4) · ln n; reason: "for sufficiently large n" given the fixed ε; same instances
--   - reading: consensus time at least e^{Ω(n^ε/k)} w.h.p. for a fixed ε (probability ≥ 1 − n^{−c}, p.2) → ∃ c > 0 and c′ > 0 chosen before ε (only N depends on ε); reason: the stronger reading of "for a fixed ε": the proof (Lemma 9.6) gives time exp(n^ε/(16(k+1))) and failure 2exp(−n^ε/(16(k+1))) with absolute constants
--   - encoding: the consensus time is at least T → the probability that none of the configurations at rounds 0, …, ⌊T⌋ is at consensus (avoidProb of the agent-level round kernel), i.e. τ₀ > ⌊T⌋; reason: τ₀ > ⌊T⌋ implies τ₀ ≥ T for the integer consensus time; the constant inside Ω(·) absorbs the integer part
--   - encoding: there exists a source-free initial configuration → ∃ ω₀ : Fin n → Bool (after ε, n, k), dynamics agentStep n k ∅; reason: the paper's quantification written out; same instances
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), sha256 8b608c8fb3d98140a2fb4da13d693fc0602cf4522527473e7ea077867327e3df, Theorem 1.3(b), p.3 (PDF p.5); proof §9.3, Lemma 9.6, pp.56–58 (PDF pp.58–60)

import Mathlib
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_MinorityDynamics_Agents

set_option autoImplicit false

open Classical

namespace MinorityDynamics.Supplement

/-- **Theorem 1.3(b) (Slow convergence regimes, small samples)** (Giakkoupis, Los, Sauerwald,
Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.3 =
PDF p.5; proof §9.3, pp.56–58 = PDF pp.58–60): "Let 17 ≤ k ≤ ((1−ε)/ln(5/4)) ln n for a fixed
ε ∈ (0, 1). There exists a source-free initial configuration for which the consensus time of
k-Minority is at least e^{Ω(n^ε/k)} w.h.p."

There are absolute constants `c > 0` (the `Ω(·)`) and `c′ > 0` (w.h.p. = probability at least
`1 − n^{−c′}`, p.2) such that for every `ε ∈ (0, 1)` there is `N` with the following property:
for every odd `n ≥ N` and odd `k` with `17 ≤ k ≤ ((1 − ε)/ln(5/4)) ln n`, some configuration
`ω₀` without sources has probability at least `1 − n^{−c′}` of avoiding consensus during rounds
`0, …, ⌊exp(c n^ε/k)⌋`.

**Formalization Note** The process is `agentStep n k ∅` of the published definition
`MinorityDynamics.Agents`. "The consensus time is at least T" is `τ₀ > ⌊T⌋`
(`avoidProb … ⌊T⌋₊ ω₀`), which implies `τ₀ ≥ T`. The constants `c, c′` are chosen before `ε`
(only `N` depends on `ε`), the stronger reading of "for a fixed ε". `n^ε` is the real power
`(n : ℝ) ^ ε`; `ln` is `Real.log`. No condition `k ≥ 8 ln n` is imposed (§9.3, p.56). -/
theorem theorem_1_3_b :
    ∃ c : ℝ, 0 < c ∧ ∃ c' : ℝ, 0 < c' ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n →
        ∀ k : ℕ, Odd k → 17 ≤ k →
          (k : ℝ) ≤ (1 - ε) / Real.log (5 / 4) * Real.log n →
          ∃ ω₀ : Fin n → Bool,
            1 - (n : ℝ) ^ (-c') ≤
              avoidProb (agentStep n k ∅) {ω | IsConsensus ω}
                ⌊Real.exp (c * (n : ℝ) ^ ε / k)⌋₊ ω₀ := by sorry

end MinorityDynamics.Supplement
