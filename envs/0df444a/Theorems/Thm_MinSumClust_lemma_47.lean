-- Prove2me | Theorems.Thm_MinSumClust_lemma_47
-- name    : MinSumClust.lemma_47
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:05.357199+00:00
-- url     : https://prove2.me/theorems/9e2d5f05-321f-4ff6-9cf3-76099ddabe5e
-- title:
--   Lemma 47 — dual feasibility of $\Gamma$-critical sets
-- statement:
--   Assume $\Gamma=r_S\gamma_{DC}$, $\gamma_{DC}=r_S\gamma_{IC}$ and $r_S>832$, with the standing assumptions of §4. For every complete run of Algorithm 3 with final dual solution $\alpha^*$, every $\Gamma$-critical set $C$ satisfies
--
--   $$\sum_{i\in C}\alpha^*_i\ \le\ f+\Gamma\cdot\mathrm{cost}(C).$$
--
--   With Observation 39 it gives Lemma 17.
--
--   Differences from the source:
--
--   - reading: Algorithm 3 with choices left open (enumeration order of (s, c), which maximizer, which client a cleaning round removes, order of simultaneous events) → every run of the run relation Alg3Step (all such choices); reason: the paper leaves these choices open; the statement holds for each of them
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Lemma 47, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumClust_IsCritical
import Definitions.Def_MinSumClust_Alg3State
import Definitions.Def_MinSumClust_Alg3Step

namespace MinSumClust

/-- **Lemma 47 (dual feasibility of critical clusters)**, p.38 (PDF p.40).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Lemma 47, p.38.

Assume `Γ = r_S γ_DC`, `γ_DC = r_S γ_IC` and `r_S > 832`. For every complete run of Algorithm 3 with
final dual solution `α*`, every Γ-critical set `C` satisfies `∑_{i ∈ C} α*_i ≤ f + Γ · cost(C)`. -/
theorem lemma_47 {n : ℕ} (P : Alg3Params n) (hP : P.Valid) (Γ : ℝ) (hΓ : Γ = P.rS * P.γDC)
    (h1 : P.γDC = P.rS * P.γIC) (h2 : 832 < P.rS) (σ : Alg3State n) (hσ : Alg3Complete P σ)
    (C : Finset (Fin n)) (hC : IsCritical P.d σ.α Γ C) :
    ∑ i ∈ C, σ.α i ≤ P.f + Γ * cost P.d C := by sorry

end MinSumClust
