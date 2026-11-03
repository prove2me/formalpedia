-- Prove2me | Theorems.Thm_OnDemandCoord_priorityAlloc_noWaste
-- name    : OnDemandCoord.priorityAlloc_noWaste
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:10.953985+00:00
-- url     : https://prove2.me/theorems/e92f472b-e1d8-4b92-ba10-d4b7d7f8f1a2
-- title:
--   A priority list is feasible and no-waste; the TFRB policy lies in $\mathcal A$ and is no-waste
-- statement:
--   **Feasibility and no waste of priority allocation** ((1), p. 8; (4), p. 11; §A.4.2, p. A6). For vacancies $\hat x\ge0$, workforce $S\ge0$ and any priority list $\sigma$, the priority allocation $a$ of Algorithm 1 satisfies:
--   1. the restrictions (1): $0\le a_i\le\hat x_i$ for all $i$ and $\sum_ia_i\le S$;
--   2. the no-waste condition (4): $\sum_ia_i=\min\{S,\sum_i\hat x_i\}$;
--   3. for every $j$, the first $j$ firms of the list together receive $\min\{S,\sum_{l\le j}\hat x_{\sigma(l)}\}$.
--
--   Consequently, for every $Q$, workforce level of the simulation, target fill rates, run data and $T\ge2$, the TFRB policy $\kappa_T$ is a Markov kernel in $\mathcal A$ and is no-waste.
--
--   This is what makes the allocation terms cancel in the system cost and in the platform's profit.
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - generalization: the no-waste condition for the TFRB policy → also the prefix identity: the first j firms of any list get min{S, Σ of their vacancies}; reason: the prefix identity is what Claim 2's proof uses; it specializes to (4) at j = n
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), §A.4.2, p. A6 (PDF 38); (1), p. 8; (4), p. 11; Algorithm 1, p. 16

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory

/-- **A priority list is feasible and no-waste**, (1) p. 8, (4) p. 11, §A.4.2 p. A6 (PDF 38),
Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13). For `x̂ ≥ 0`, `r ≥ 0` and any list `σ`: the priority allocation satisfies (1), it
allocates `min {r, ∑_i x̂_i}`, and its first `j` firms get `min {r, ∑_{l < j} x̂_{σ l}}` together.
Hence the TFRB policy lies in `𝒜` and is no-waste. -/
theorem priorityAlloc_noWaste {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Q : Fin n → ℝ) (s : ℝ) (β : Fin n → ℝ) (run : RunData n s) (T : ℕ) (hT : 2 ≤ T) :
    (∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (r : ℝ), 0 ≤ x → 0 ≤ r →
      IsFeasibleAlloc x r (priorityAlloc σ x r) ∧
      ∑ i, priorityAlloc σ x r i = min r (∑ i, x i) ∧
      ∀ j : ℕ, j ≤ n →
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < j), priorityAlloc σ x r (σ l) =
          min r (∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < j), x (σ l))) ∧
    IsPolicy (M.tfrb Q s β run T) ∧ IsNoWaste (M.tfrb Q s β run T) := by sorry

end OnDemandCoord
