-- Prove2me | Theorems.Thm_MinSumClust_lemma_17
-- name    : MinSumClust.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:32.860983+00:00
-- url     : https://prove2.me/theorems/52a4c0a3-6d34-4a0b-b724-c500ec20e4ef
-- title:
--   Lemma 17 — dual feasibility of the final dual solution of Algorithm 3
-- statement:
--   Assume $\Gamma=r_S\gamma_{DC}$, $\gamma_{DC}=r_S\gamma_{IC}$ and $r_S>832$, with the standing assumptions of §4. For every complete run of Algorithm 3 with final dual solution $\alpha^*$ and every $C\subseteq D$,
--
--   $$\sum_{i\in C}\alpha^*_i\ \le\ f+\Gamma\cdot\mathrm{cost}(C).$$
--
--   So $\alpha^*$ is feasible for the Lagrangian dual (MinSum-Lag-Dual) up to the factor $\Gamma$ on connection costs, and weak duality gives $\sum_i\alpha^*_i\le k f+\Gamma\,\mathrm{opt}$ in Theorem 2.
--
--   Differences from the source:
--
--   - reading: Algorithm 3 with choices left open (enumeration order of (s, c), which maximizer, which client a cleaning round removes, order of simultaneous events) → every run of the run relation Alg3Step (all such choices); reason: the paper leaves these choices open; the statement holds for each of them
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Lemma 17, p.25 (PDF p.27); restated p.34 (PDF p.36)

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumClust_Alg3State
import Definitions.Def_MinSumClust_Alg3Step

namespace MinSumClust

/-- **Lemma 17 (dual feasibility)**, p.25 (PDF p.27); restated p.34 (PDF p.36).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Lemma 17, p.25.

Assume `Γ = r_S γ_DC`, `γ_DC = r_S γ_IC` and `r_S > 832`. For every complete run of Algorithm 3 with
final dual solution `α*`, every `C ⊆ D` satisfies `∑_{i ∈ C} α*_i ≤ f + Γ · cost(C)`. -/
theorem lemma_17 {n : ℕ} (P : Alg3Params n) (hP : P.Valid) (Γ : ℝ) (hΓ : Γ = P.rS * P.γDC)
    (h1 : P.γDC = P.rS * P.γIC) (h2 : 832 < P.rS) (σ : Alg3State n) (hσ : Alg3Complete P σ) :
    ∀ C : Finset (Fin n), ∑ i ∈ C, σ.α i ≤ P.f + Γ * cost P.d C := by sorry

end MinSumClust
