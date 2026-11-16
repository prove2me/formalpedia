-- Prove2me | Theorems.Thm_MinorityDynamics_Supplement_theorem_1_3_a
-- name    : MinorityDynamics.Supplement.theorem_1_3_a
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:03:41.599351+00:00
-- url     : https://prove2.me/theorems/688dd41a-f3bc-413e-a030-32e2266eb8d9
-- title:
--   Theorem 1.3(a) — under the residue condition (1.3), a single source needs $e^{\Omega(k)}$ rounds w.h.p.
-- statement:
--   In $k$-Minority each of $n$ agents holds one of two opinions; in each synchronous round every non-source agent samples $k$ agents uniformly with replacement (itself and any sources included), independently, and adopts the less frequent opinion present in its sample (a unanimous sample is adopted); sources never change their opinion. The **consensus time** $\tau_0$ is the first round $t\ge0$ at which all agents hold the same opinion. Throughout, $n$ and $k$ are odd and $\ln$ is the natural logarithm.
--
--   Suppose that
--
--   $$k\ge 8\ln n,\qquad k=e^{o(\sqrt{\ln n})},\qquad \ln 5\le \frac{k^d}{n}\le \ln 7\quad\text{for some } d\in\mathbb N.\qquad(1.3)$$
--
--   There are absolute constants $c,c'>0$ such that, for all sufficiently large $n$: for every agent $i$ and opinion $b$, if $i$ is the only source, holds $b$, and every other agent initially holds the opposite opinion, then with probability at least $1-n^{-c'}$
--
--   $$\tau_0 \;>\; \big\lfloor e^{c k}\big\rfloor .$$
--
--   With a single source, an unfavourable residue of $\ln n/\ln k$ (condition (1.3), as opposed to (1.1) of Theorem 1.1) makes consensus exponentially slow in $k$; so some restriction on the residue is necessary for a uniform polylogarithmic upper bound with sources.
--
--   **Formalization Note** The dynamics is `agentStep n k {i}` (source set $\{i\}$). "$k=e^{o(\sqrt{\ln n})}$ for sufficiently large $n$" is: there are $\varepsilon>0$ and $N$ such that the claim holds for every odd $n\ge N$, odd $k$ and $d\in\mathbb N$ with (1.3) and $\ln k\le\varepsilon\sqrt{\ln n}$; $k^d/n$ is a real quotient.
--
--   Differences from the source:
--   - encoding: (1.3): k ≥ 8 ln n, k = e^{o(√(ln n))}, ln 5 ≤ k^d/n ≤ ln 7 for some d ∈ ℕ; n, k odd; for sufficiently large n (p.2) → ∃ ε > 0, ∃ N such that the claim holds for every odd n ≥ N, odd k and d ∈ ℕ with 8 ln n ≤ k, ln k ≤ ε√(ln n), ln 5 ≤ k^d/n ≤ ln 7 (real quotient); reason: with c, c′ fixed first this is equivalent to the sequence reading of k = e^{o(√ln n)}; "for some d" in a hypothesis is "for every d" satisfying it; same instances
--   - reading: consensus time at least e^{Ω(k)} w.h.p. (probability ≥ 1 − n^{−c} for some constant c > 0, p.2) → ∃ c > 0 (the Ω-constant) and c′ > 0 (failure n^{−c′}) chosen first, absolute; reason: the stronger reading: constants independent of the sample-size sequence; the proof (§9) gives explicit absolute constants
--   - encoding: the consensus time is at least T → the probability that none of the configurations at rounds 0, …, ⌊T⌋ is at consensus (avoidProb of the agent-level round kernel), i.e. τ₀ > ⌊T⌋; reason: τ₀ > ⌊T⌋ implies τ₀ ≥ T for the integer consensus time; the constant inside Ω(·) absorbs the integer part
--   - encoding: starting with a single source as the sole holder of its opinion → every source agent i, every opinion b, every ω₀ with ω₀ i = b and ω₀ j = !b for j ≠ i; dynamics agentStep n k {i}; reason: the paper's single-source configurations written out, universally quantified; same instances
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), sha256 8b608c8fb3d98140a2fb4da13d693fc0602cf4522527473e7ea077867327e3df, Theorem 1.3(a), (1.3), p.3 (PDF p.5); proof §9.2, pp.52–56 (PDF pp.54–58)

import Mathlib
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_MinorityDynamics_Agents

set_option autoImplicit false

open Classical

namespace MinorityDynamics.Supplement

/-- **Theorem 1.3(a) (Slow convergence regimes, one source)** (Giakkoupis, Los, Sauerwald,
Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.3 =
PDF p.5; proof §9.2, pp.52–56 = PDF pp.54–58): "Suppose that
k ≥ 8 ln n, k = e^{o(√(ln n))}, ln 5 ≤ k^d/n ≤ ln 7, for some d ∈ N. (1.3)
Starting with a single source as the sole holder of its opinion, the consensus time of
k-Minority is at least e^{Ω(k)} w.h.p."

There are absolute constants `c > 0` (the `Ω(·)`) and `c′ > 0` (w.h.p. = probability at least
`1 − n^{−c′}`, p.2) such that, for all sufficiently large odd `n`, odd `k` and `d ∈ ℕ` satisfying
(1.3), every source agent `i`, every opinion `b` and every configuration `ω₀` in which `i` holds
`b` and every other agent holds the other opinion, k-Minority with source set `{i}` avoids
consensus during rounds `0, …, ⌊e^{c k}⌋` with probability at least `1 − n^{−c′}`.

**Formalization Note** The process is `agentStep n k {i}` of the published definition
`MinorityDynamics.Agents`: the source `i` keeps its opinion, every other agent samples `k`
agents (the source included) and adopts the minority opinion of its sample. "The consensus time
is at least T" is `τ₀ > ⌊T⌋` (`avoidProb … ⌊T⌋₊ ω₀`), which implies `τ₀ ≥ T`.
"k = e^{o(√(ln n))}" with "for sufficiently large n" is: there are `ε > 0` and `N` such that the
claim holds for all odd `n ≥ N` with `ln k ≤ ε √(ln n)`; with `c, c′` chosen first this is
equivalent to the sequence reading. "For some d ∈ N" in a hypothesis is "for every `d`
satisfying it"; `k^d/n` is the real quotient. -/
theorem theorem_1_3_a :
    ∃ c : ℝ, 0 < c ∧ ∃ c' : ℝ, 0 < c' ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n →
      ∀ k : ℕ, Odd k → ∀ d : ℕ,
        8 * Real.log n ≤ (k : ℝ) → Real.log k ≤ ε * Real.sqrt (Real.log n) →
        Real.log 5 ≤ (k : ℝ) ^ d / n → (k : ℝ) ^ d / n ≤ Real.log 7 →
        ∀ (i : Fin n) (b : Bool) (ω₀ : Fin n → Bool), ω₀ i = b → (∀ j, j ≠ i → ω₀ j = !b) →
          1 - (n : ℝ) ^ (-c') ≤
            avoidProb (agentStep n k {i}) {ω | IsConsensus ω}
              ⌊Real.exp (c * k)⌋₊ ω₀ := by sorry

end MinorityDynamics.Supplement
