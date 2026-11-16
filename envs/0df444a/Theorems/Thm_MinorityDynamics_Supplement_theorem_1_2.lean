-- Prove2me | Theorems.Thm_MinorityDynamics_Supplement_theorem_1_2
-- name    : MinorityDynamics.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:03:08.028128+00:00
-- url     : https://prove2.me/theorems/ca89c2ec-c5ce-4c9d-bc0f-a64f77c08048
-- title:
--   Theorem 1.2 — without sources, some configuration needs $\Omega(\ln^2 n/(\ln k\ln\ln n))$ rounds w.h.p. for $8\ln n\le k=n^{o(1)}$
-- statement:
--   In $k$-Minority each of $n$ agents holds one of two opinions; in each synchronous round every non-source agent samples $k$ agents uniformly with replacement (itself and any sources included), independently, and adopts the less frequent opinion present in its sample (a unanimous sample is adopted); sources never change their opinion. The **consensus time** $\tau_0$ is the first round $t\ge0$ at which all agents hold the same opinion. Throughout, $n$ and $k$ are odd and $\ln$ is the natural logarithm.
--
--   There are absolute constants $c,c'>0$ such that the following holds for all sufficiently large $n$. Let $k\ge 8\ln n$ with $k=n^{o(1)}$. Then there is an initial configuration without sources from which, with probability at least $1-n^{-c'}$,
--
--   $$\tau_0 \;>\; \Big\lfloor \frac{c\,\ln^2 n}{\ln k\,\ln\ln n}\Big\rfloor .$$
--
--   In the regime of Theorem 1.1 this lower bound is within a factor $\ln\ln n$ of the upper bound $O(\ln^2 n/\ln k)$, so polylogarithmic sample sizes cannot give logarithmic-time consensus. No residue condition is assumed.
--
--   **Formalization Note** The dynamics is the published agent-level kernel `agentStep n k ∅`; "$\tau_0>\lfloor T\rfloor$" is the probability `avoidProb` that rounds $0,\dots,\lfloor T\rfloor$ all avoid consensus. "$k=n^{o(1)}$ for sufficiently large $n$" is: there are $\varepsilon>0$ and $N$ such that the claim holds for every odd $n\ge N$ and odd $k$ with $8\ln n\le k\le n^{\varepsilon}$.
--
--   Differences from the source:
--   - encoding: for any k ≥ 8 ln n and k = n^{o(1)}; n, k odd; for sufficiently large n (p.2) → ∃ ε > 0, ∃ N such that the claim holds for every odd n ≥ N and odd k with 8 ln n ≤ k ≤ n^ε; reason: with c, c′ fixed first this is equivalent to the reading for every sequence k = k(n) = n^{o(1)}, k ≥ 8 ln n, for all sufficiently large n; same instances
--   - reading: consensus time Ω(ln² n/(ln k ln ln n)) w.h.p. (probability ≥ 1 − n^{−c} for some constant c > 0, p.2) → ∃ c > 0 (the Ω-constant) and c′ > 0 (failure n^{−c′}) chosen first, absolute; reason: the stronger reading: constants independent of the sample-size sequence; the proof (§9) gives explicit absolute constants
--   - encoding: the consensus time is at least T → the probability that none of the configurations at rounds 0, …, ⌊T⌋ is at consensus (avoidProb of the agent-level round kernel), i.e. τ₀ > ⌊T⌋; reason: τ₀ > ⌊T⌋ implies τ₀ ≥ T for the integer consensus time; the constant inside Ω(·) absorbs the integer part
--   - encoding: there exists a source-free initial configuration → ∃ ω₀ : Fin n → Bool (after n and k), dynamics agentStep n k ∅; reason: the paper's quantification written out; same instances
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), sha256 8b608c8fb3d98140a2fb4da13d693fc0602cf4522527473e7ea077867327e3df, Theorem 1.2, p.2 (PDF p.4); proof §9.1, pp.48–52 (PDF pp.50–54)

import Mathlib
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_MinorityDynamics_Agents

set_option autoImplicit false

open Classical

namespace MinorityDynamics.Supplement

/-- **Theorem 1.2 (Lower bound)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with
Small Samples*, manuscript (STOC 2027 submission), p.2 = PDF p.4; proof §9.1, pp.48–52 =
PDF pp.50–54): "For any k ≥ 8 ln n and k = n^{o(1)}, there exists a source-free initial
configuration from which the consensus time of k-Minority is Ω(ln² n/(ln k ln ln n)) w.h.p."

There are absolute constants `c > 0` (the `Ω(·)`) and `c′ > 0` (w.h.p. = probability at least
`1 − n^{−c′}`, p.2) such that, for all sufficiently large odd `n` and odd `k` with
`8 ln n ≤ k ≤ n^ε`, some configuration `ω₀` without sources has probability at least
`1 − n^{−c′}` of avoiding consensus during rounds `0, …, ⌊c (ln n)²/(ln k · ln ln n)⌋`.

**Formalization Note** The process is the agent-level k-Minority dynamics `agentStep n k ∅` of
the published definition `MinorityDynamics.Agents` (no sources). "The consensus time is at least
T" is `τ₀ > ⌊T⌋`, i.e. `avoidProb … ⌊T⌋₊ ω₀`, the probability that none of the configurations at
rounds `0, …, ⌊T⌋` is at consensus; this implies `τ₀ ≥ T`. "k = n^{o(1)}" with "for sufficiently
large n" is: there are `ε > 0` and `N` such that the claim holds for all odd `n ≥ N` and odd `k`
with `8 ln n ≤ k ≤ n^ε`; with `c, c′` chosen first this is equivalent to the paper's reading for
every sequence `k = k(n) = n^{o(1)}`. `ln` is `Real.log`; no residue condition is imposed
(p.48). -/
theorem theorem_1_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ c' : ℝ, 0 < c' ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n →
      ∀ k : ℕ, Odd k → 8 * Real.log n ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ ε →
        ∃ ω₀ : Fin n → Bool,
          1 - (n : ℝ) ^ (-c') ≤
            avoidProb (agentStep n k ∅) {ω | IsConsensus ω}
              ⌊c * Real.log n ^ 2 / (Real.log k * Real.log (Real.log n))⌋₊ ω₀ := by sorry

end MinorityDynamics.Supplement
