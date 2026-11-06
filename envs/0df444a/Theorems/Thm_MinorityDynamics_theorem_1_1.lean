-- Prove2me | Theorems.Thm_MinorityDynamics_theorem_1_1
-- name    : MinorityDynamics.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:48.226132+00:00
-- url     : https://prove2.me/theorems/60c9d153-5557-4902-a6ff-c2c780f8e6c0
-- title:
--   Theorem 1.1 — k-Minority reaches consensus within $O(\ln^2 n/\ln k)$ rounds w.h.p., without sources and with $\varrho$ sources
-- statement:
--   Let $n$ and $k$ be odd. In $k$-Minority each of $n$ agents holds one of two opinions; in each synchronous round every non-source agent samples $k$ agents uniformly with replacement (itself and the sources included) and adopts the less frequent opinion present in its sample (a unanimous sample is adopted); sources never change their opinion. Suppose that
--   $$k\ge(\ln n)^{21/10},\qquad k=n^{o(1)},\qquad 2\ln n\le\frac{k^d}{n}\le\frac15(\ln n)^{21/20}\quad\text{for some }d\in\mathbb N.\qquad(1.1)$$
--   Then there are constants $C,c>0$ such that, for all sufficiently large $n$:
--
--   1. from every source-free initial configuration, $k$-Minority reaches consensus within $C\ln^2 n/\ln k$ rounds with probability at least $1-n^{-c}$;
--   2. the same holds for every initial configuration with $\varrho$ sources sharing the same opinion, provided that
--   $$1\le\varrho\le\frac{\ln k}{144}\sqrt{\frac{k}{(\ln n)^{81/20}}}.\qquad(1.2)$$
--
--   This is the paper's main result: polylogarithmic samples suffice for fast consensus and bit dissemination under the residue condition.
--
--   Differences from the source:
--   - encoding: under (1.1): k ≥ L^{21/10}, k = n^{o(1)}, 2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20} for some d ∈ ℕ; n, k odd; for sufficiently large n (p.2) → ∃ ε > 0, ∃ N such that the claim holds for every odd n ≥ N, odd k and d ∈ ℕ with (ln n)^{21/10} ≤ k ≤ n^ε and 2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20} (real quotient); reason: equivalent to the sequence reading of k = n^{o(1)} for all sufficiently large n; "for some d" in a hypothesis is "for every d" satisfying it; same instances
--   - reading: within O(ln² n/ln k) rounds w.h.p. (probability ≥ 1 − n^{−c} for some constant c > 0, p.2) → ∃ C > 0 and c > 0 chosen first (absolute), shared by both clauses; reason: the stronger reading, constants independent of the sample-size sequence; the proof gives C·DL + D + 2 rounds and failure 5n^{−1/2} or 6n^{−1/2}
--   - encoding: "reaches consensus within T rounds" → the probability that none of the configurations at rounds 0, …, ⌊T⌋ is at consensus is ≤ n^{−c} (avoidProb of the agent-level round kernel); reason: τ ≤ T iff τ ≤ ⌊T⌋ for the integer consensus time; same event
--   - encoding: ϱ sources sharing the same opinion; every initial configuration → every source set Src with |Src| = ϱ, every opinion b, every configuration with ω₀(i) = b on Src; reason: the paper's quantification written out; same instances
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Theorem 1.1, p.2, (1.1)–(1.2)

import Mathlib
import Definitions.Def_MinorityDynamics_Kernel
import Definitions.Def_MinorityDynamics_Agents

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Theorem 1.1 (Upper bound)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.2 = PDF p.4): "Suppose that
k ≥ (ln n)^{21/10}, k = n^{o(1)}, 2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20}, for some d ∈ N. (1.1)
From every source-free initial configuration, k-Minority reaches consensus within O(ln² n/ ln k)
rounds w.h.p. The same is true for every initial configuration with ϱ sources sharing the same
opinion, provided that 1 ≤ ϱ ≤ (ln k/144) √(k/(ln n)^{81/20}). (1.2)"

Both clauses, with shared absolute constants `C` (the `O(·)`) and `c` (w.h.p. = probability at least
`1 − n^{−c}`, p.2): (i) from every configuration without sources, (ii) for every `ϱ` in the range
(1.2), every source set of `ϱ` agents, every source opinion `b` and every configuration in which
the sources hold `b`, the probability that k-Minority has not reached consensus within
`⌊C (ln n)²/ln k⌋` rounds is at most `n^{−c}`.

**Formalization Note** The process is the agent-level dynamics (`agentStep`): every non-source
agent samples `k` agents uniformly with replacement among all `n` (itself and the sources
included), independently, and adopts the less frequent opinion present in its sample; sources
keep their opinion. "Reaches consensus within T rounds" is `τ ≤ ⌊T⌋` for the first round `τ` at
which all agents agree, so the failure event is that rounds `0, …, ⌊T⌋` all avoid consensus.
"k = n^{o(1)}" with "for sufficiently large n" (p.2) is: there are `ε > 0` and `N` such that the
claim holds for all odd `n ≥ N`, odd `k` and `d ∈ ℕ` with `(ln n)^{21/10} ≤ k ≤ n^ε` and
`2 ln n ≤ k^d/n ≤ (1/5)(ln n)^{21/20}` (real quotient), which is equivalent to the paper's
reading for every sequence `k = k(n) = n^{o(1)}`. `C` and `c` are absolute (chosen first). -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n →
      ∀ k : ℕ, Odd k → ∀ d : ℕ,
    Real.log n ^ ((21 : ℝ) / 10) ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ ε →
    2 * Real.log n ≤ (k : ℝ) ^ d / n → (k : ℝ) ^ d / n ≤ (1 / 5) * Real.log n ^ ((21 : ℝ) / 20) →
      (∀ ω₀ : Fin n → Bool,
        avoidProb (agentStep n k ∅) {ω | IsConsensus ω}
            ⌊C * Real.log n ^ 2 / Real.log k⌋₊ ω₀ ≤ (n : ℝ) ^ (-c)) ∧
      (∀ ϱ : ℕ, 1 ≤ ϱ →
        (ϱ : ℝ) ≤ Real.log k / 144 * Real.sqrt ((k : ℝ) / Real.log n ^ ((81 : ℝ) / 20)) →
        ∀ (Src : Finset (Fin n)), Src.card = ϱ → ∀ (b : Bool) (ω₀ : Fin n → Bool),
          (∀ i ∈ Src, ω₀ i = b) →
          avoidProb (agentStep n k Src) {ω | IsConsensus ω}
              ⌊C * Real.log n ^ 2 / Real.log k⌋₊ ω₀ ≤ (n : ℝ) ^ (-c)) := by sorry

end MinorityDynamics
