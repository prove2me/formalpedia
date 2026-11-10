-- Prove2me | Theorems.Thm_GoodHypotheses_Proper_fact_2_1
-- name    : GoodHypotheses.Proper.fact_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:15:16.207115+00:00
-- url     : https://prove2.me/theorems/3a9521e1-6aea-46a0-8c97-07cfe4cb8889
-- title:
--   Fact 2.1 — valid scores give the proper guarantee: a minimum-score hypothesis has d_TV ≤ 3OPT + 3ε, found deterministically in O(n) time
-- statement:
--   Let $h_1,\dots,h_n,p$ be probability densities, $\varepsilon>0$ and $\sigma_1,\dots,\sigma_n$ valid scores. Every hypothesis $h_{out}$ of minimum score ($\sigma_{out}=\min_i\sigma_i$, ties broken arbitrarily) satisfies
--   $$d_{TV}(h_{out},p)\le3\,\mathrm{OPT}+3\varepsilon,$$
--   and such an index is found by a deterministic algorithm in time $O(n)$: one fixed oracle-free program and one universal constant $C$ such that, for every $n\ge1$ and all scores in memory, the program halts within $Cn+C$ steps with a minimum-score index in its output register.
--
--   Differences from the source:
--
--   - reading: "selects a hypothesis achieving the optimal proper guarantee" → every index of minimum score satisfies d_TV(h_i, p) ≤ 3·OPT + 3ε; reason: the guarantee derived directly above Fact 2.1 on p. 5
--   - reading: "there exists an algorithm running in time O(n) which deterministically selects" → ∃ C > 0, ∃ an Admissible OracleFree program such that for every n ≥ 1, every σ and every tape it halts within C·n + C steps with a minimizing index in pointer register 0; reason: machine reading of 'time'; the additive C covers the constant overhead; OracleFree makes it deterministic
--   - reading: "runs in time", constant-time sampling and density queries (pp. 1–2, §3) → the number of executed instructions of an Admissible program of the unit-cost randomized real RAM `Machine` (SmaleNinth core, integer memory, exp, log, uniform tape, opaque X-registers with sampleP, sampleH, evalH, halt; rational literals, no floor); reason: the paper names no machine; every arithmetic operation and every oracle call costs one unit
--   - encoding: scores σ_1, …, σ_n given → σ in real memory cells 0, …, n − 1 and n in integer memory cell 0; reason: input layout
--   - encoding: items i ∈ [n] = {1, …, n} → i : Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), p. 5, Fact 2.1 and the derivation above it

import Mathlib
import Definitions.Def_GoodHypotheses_Proper_Densities
import Definitions.Def_GoodHypotheses_Proper_Machine

open MeasureTheory

namespace GoodHypotheses.Proper

/-- Fact 2.1 (p. 5), with "the optimal proper guarantee" as derived directly above it on p. 5.
(1) For probability densities `h_1, …, h_n, p`, `ε > 0` and valid scores `σ` (Definition 1),
every index `i` of minimum score (ties broken arbitrarily: every minimizer) satisfies
`dTV(h_i, p) ≤ 3 OPT + 3ε`. (2) One fixed deterministic, oracle-free program and one universal
constant `C` such that, for every `n ≥ 1` and all scores `σ_1, …, σ_n` in memory, the program
halts within `C n + C` steps with a minimum-score index in pointer register `0`. -/
theorem fact_2_1 :
    (∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (n : ℕ) (h : Fin n → X → ℝ) (p : X → ℝ)
        (ε : ℝ) (σ : Fin n → ℝ),
        1 ≤ n → (∀ i, IsProbDensity μ (h i)) → IsProbDensity μ p → 0 < ε →
        ValidScores μ p h ε σ →
        ∀ i, (∀ j, σ i ≤ σ j) → tvDist μ (h i) p ≤ 3 * OPT μ p h + 3 * ε) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧ OracleFree P ∧
      ∀ (n : ℕ) (σ : Fin n → ℝ) (ω : Tape Unit n), 1 ≤ n →
        HaltsWithin P (fun _ _ => 0) ω (scoresInput Unit σ) (C * n + C) ∧
        ∃ i, outIndex P (fun _ _ => 0) ω (scoresInput Unit σ) = some i ∧ ∀ j, σ i ≤ σ j) := by sorry

end GoodHypotheses.Proper
