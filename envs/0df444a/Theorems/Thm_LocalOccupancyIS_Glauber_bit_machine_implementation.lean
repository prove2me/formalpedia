-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_bit_machine_implementation
-- name    : LocalOccupancyIS.Glauber.bit_machine_implementation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:17:50.530206+00:00
-- url     : https://prove2.me/theorems/f3eb76a5-afd2-49b9-9f46-aa3e82e09701
-- title:
--   Exact fair-bit implementation law and expected polynomial cost
-- statement:
--   Consider the prescribed fair-bit Glauber machine on a graph with $n>0$ vertices, with degree and biclique-size inputs at most $n$, a rational density input $b$, and an initial independent set $I$. Suppose its first successful preprocessing stage is $h$, with
--
--   $$1\le h\le20(n+1)^2+2,$$
--
--   and the returned integer satisfies $1\le q\le n+2$. The first-stage hypothesis means that every earlier positive stage returns no result and stage $h$ returns the stated integer and rational enclosure endpoints.
--
--   There is an absolute constant $B\ge10^6$, preceding all these inputs, such that for every nonnegative integer $m$, the machine has total output mass one, its output is a probability distribution on independent sets, and its output law is exactly the amplified random-scan Glauber law at fugacity $1/q$, with $\max\{1,n^8\}$ updates in each of $\max\{1,n^3(m+1)\}$ independent runs. The machine retains the largest visited independent set and resets to $I$ between runs.
--
--   Its charged expected bit cost satisfies
--
--   $$\mathbb E[\mathrm{cost}]\le B\bigl(n+\operatorname{ratBits}(b)+m+\operatorname{bits}(t)+1\bigr)^{1000}.$$
--
--   The cost includes input reading, rational preprocessing, graph operations, records, resets, integer bookkeeping, and unbounded rejection loops. This theorem supplies the execution and complexity component of the rational-input implementation; the density assumptions and the quantitative first-stage bound are established separately when applying it to Corollary 4.
-- source:
--   Davies and Tan, Large independent sets via neighborhood block dynamics, Glauber dynamics, and local occupancy, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf, Corollary 4 and Remark 1 p.6, implementation discussion §§6 pp.19–20; quantitative execution conventions in the mission BitExecution and GoalInterface definitions.

import Definitions.Def_LocalOccupancyIS_Glauber_GoalInterface

namespace LocalOccupancyIS.Glauber
theorem bit_machine_implementation :
    ∃ B : ℝ, 1000000 ≤ B ∧
    ∀ n Δ t : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
    ∀ b : ℚ, ∀ I : State G, ∀ m h q : ℕ, ∀ l u : ℚ,
      0 < n → Δ ≤ n → t ≤ n → 1 ≤ h → h ≤ 20*(n+1)^2+2 → 1 ≤ q → q ≤ n+2 →
      (∀ j : ℕ,1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1=none) →
      ((parameterStage Δ t b h).run 0).1=some (q,l,u) →
      (∑ σ : Fin n → Bool,bitLaw G Δ t b I.val m σ)=1 ∧
      MarkovMixing.IsDist (bitOutput G Δ t b I m) ∧
      bitOutput G Δ t b I m=amplifiedLaw G (1/(q:ℝ)) I (bitHorizon n) (bitRepeats n m) ∧
      expectedBitCost G Δ t b I m ≤ ENNReal.ofReal (B*(n+ratBits b+m+bits t+1)^1000) := by sorry
end LocalOccupancyIS.Glauber
