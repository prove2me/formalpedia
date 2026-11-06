-- Prove2me | Theorems.Thm_MemQueryFeas_nyd83_bound
-- name    : MemQueryFeas.nyd83_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:59.033449+00:00
-- url     : https://prove2.me/theorems/bced69bc-f796-4eb1-b12a-8ac7c0c8912e
-- title:
--   Proof of Theorem 1, [NYD83] step — the memory-independent $\Omega(d\log(1/\epsilon))$ query bound
-- statement:
--   In the model of Theorem 1: there are $c>0$ and $d_0$ such that for all $d\ge d_0$, $0<\varepsilon\le e^{-d}$ and every memory size $M$,
--   1. every randomized $M$-bit algorithm that solves feasibility problems of accuracy $\varepsilon$ within $T$ queries with probability $2/3$ against valid measurable adaptive oracles has $T\ge c\,d\log(1/\varepsilon)$;
--   2. every measurable deterministic $M$-bit algorithm that solves them within $T$ queries against valid non-adaptive oracles has $T\ge c\,d\log(1/\varepsilon)$.
--
--   The resisting oracle of Nemirovski and Yudin gives this bound irrespective of memory; in the high-memory regime it already achieves the exponent of Theorem 1.
--
--   Differences from the source:
--   - reading: "the resisting separation oracle in [NYD83] that achieves the d log 1/ϵ query complexity" → both clauses of Theorem 1's model with bound c·d·log₂(1/ε), for every memory size M; reason: this is what "this also achieves the desired exponent" uses
--   - reading: d sufficiently large → ∃ d₀, uniform in all other parameters; reason: the usual meaning of the phrase
--   - generalization: success against every valid adaptive oracle → success required only against deterministic, measurable adaptive oracles valid at every point; reason: a weaker hypothesis; randomized oracles are mixtures of these
--   - generalization: Q contains a Euclidean ball of radius ε → Q contains a closed ball of radius ε; reason: fewer instances in the success hypothesis
--   - generalization: i.i.d. fresh randomness for the query and update maps → one fresh draw per round shared by both maps; reason: separate draws are the case of a product space
--   - reading: randomized and deterministic algorithms (measurability not stated) → measurable maps (RandMemAlg fields; DetMemAlg.IsMeasurable); reason: standing convention: success probabilities of runs are defined for measurable algorithms
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Proof of Theorem 1, p.31 (PDF p.32)

import Mathlib
import Definitions.Def_MemQueryFeas_SucceedsAdaptive
import Definitions.Def_MemQueryFeas_SucceedsNonAdaptive
import Definitions.Def_MemQueryFeas_DetMemAlg_IsMeasurable

namespace MemQueryFeas

/-- **The memory-independent `d log(1/ϵ)` lower bound (proof of Theorem 1, [NYD83] step).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026),
proof of Theorem 1, p.31 (PDF p.32): "Here, instead of using the transform separation oracle, we
simply apply the resisting separation oracle in [NYD83] that achieves the `d log 1/ϵ` query
complexity. In particular, this also achieves the desired exponent."

In the model of Theorem 1: there are `c > 0` and `d₀` such that for `d ≥ d₀`, `0 < ε ≤ e^{−d}` and any
memory `M`, (a) every randomized `M`-bit algorithm succeeding within `T` queries with probability
`2/3` against valid measurable adaptive oracles, and (b) every measurable deterministic `M`-bit
algorithm succeeding within `T` queries against valid non-adaptive oracles, have
`T ≥ c d log₂(1/ε)`.

**Formalization Note.** Stated in the model of Theorem 1 (same success notions), for every memory
size. log is base 2. -/
theorem nyd83_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-(d : ℝ)) → ∀ M : ℕ,
        (∀ (alg : RandMemAlg d M) (T : ℕ), SucceedsAdaptive alg ε T →
          c * d * Real.logb 2 (1 / ε) ≤ (T : ℝ)) ∧
        (∀ (alg : DetMemAlg d M) (T : ℕ), alg.IsMeasurable → SucceedsNonAdaptive alg ε T →
          c * d * Real.logb 2 (1 / ε) ≤ (T : ℝ)) := by sorry

end MemQueryFeas
