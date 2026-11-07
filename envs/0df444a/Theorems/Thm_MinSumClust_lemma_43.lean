-- Prove2me | Theorems.Thm_MinSumClust_lemma_43
-- name    : MinSumClust.lemma_43
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:12.225753+00:00
-- url     : https://prove2.me/theorems/e520ca90-5dc6-4758-b56f-7ad3954019ae
-- title:
--   Lemma 43 — dual feasibility of available sets throughout Algorithm 3
-- statement:
--   Assume $\gamma_{DC}\ge\gamma_{IC}r_S$ and $r_S\ge 6$, with the standing assumptions of §4. Throughout Algorithm 3, every set $S$ that is available for the current dependency forest satisfies
--
--   $$\sum_{i\in S}\alpha_i\ \le\ f+4\gamma_{DC}\cdot\mathrm{cost}(S).\qquad(20)$$
--
--   This invariant is the key input of the dual feasibility Lemma 47.
--
--   Differences from the source:
--
--   - reading: throughout the algorithm → in every state reachable by a run of Algorithm 3, including states part-way through a growth phase; reason: the most inclusive reading of "throughout"
--   - reading: Algorithm 3 with choices left open (enumeration order of (s, c), which maximizer, which client a cleaning round removes, order of simultaneous events) → every run of the run relation Alg3Step (all such choices); reason: the paper leaves these choices open; the statement holds for each of them
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Lemma 43, p.35 (PDF p.37), display (20)

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumClust_Alg3State
import Definitions.Def_MinSumClust_Alg3Step

namespace MinSumClust

/-- **Lemma 43 (dual feasibility of available sets)**, p.35 (PDF p.37), display (20).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Lemma 43, p.35.

Assume `γ_DC ≥ γ_IC r_S` and `r_S ≥ 6`. Throughout Algorithm 3, every available set `S` satisfies
`∑_{i ∈ S} α_i ≤ f + 4γ_DC · cost(S)`.

**Formalization Note.** "Throughout the algorithm" is every state reachable by a run
(`Alg3Reachable`), including states part-way through a growth phase; "available" is with respect to
the forest of that state. -/
theorem lemma_43 {n : ℕ} (P : Alg3Params n) (hP : P.Valid) (h1 : P.γIC * P.rS ≤ P.γDC)
    (h2 : 6 ≤ P.rS) (σ : Alg3State n) (hσ : Alg3Reachable P σ) (S : Finset (Fin n))
    (hS : Available σ S) :
    ∑ i ∈ S, σ.α i ≤ P.f + 4 * P.γDC * cost P.d S := by sorry

end MinSumClust
