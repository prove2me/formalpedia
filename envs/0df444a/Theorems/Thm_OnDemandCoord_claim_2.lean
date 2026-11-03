-- Prove2me | Theorems.Thm_OnDemandCoord_claim_2
-- name    : OnDemandCoord.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:04.991251+00:00
-- url     : https://prove2.me/theorems/44fe85a0-92e2-49c6-a2e5-a9e3d5015266
-- title:
--   Claim 2: under any priority list, the expected reward of the first $j$ firms is $\le 0$
-- statement:
--   **Claim 2** (p. A4). Let $S\ge0$, and let $\beta$ be feasible for the linear program (8) at $(Q,S)$: $\beta\ge0$ and $\sum_{i\in U}\beta_i\mathbb E[\hat X_i]\le\mathbb E[\min\{S,\sum_{i\in U}\hat X_i\}]$ for all $U\subseteq I$. Write the reward of firm $i$ as $R_i=\beta_i\mathbb E[\hat X_i]-A_i$.
--   1. For every priority list $\sigma$ and every $j$, under the priority allocation of $\hat X$ in the order $\sigma$, $$\sum_{l=1}^{j}\mathbb E\big[R_{\sigma(l)}\big]\le 0 .$$
--   2. In the simulation of Algorithm 1 (any run data, any $T$, any period $t\in\{2,\dots,T\}$), given that the list of period $t$ is $\sigma$: for every $j$, $$\mathbb E\Big[\mathbf 1\{L(t)=\sigma\}\sum_{l=1}^{j}\big(\beta_{\sigma(l)}\mathbb E[\hat X_{\sigma(l)}]-A_{\sigma(l)}(t)\big)\Big]\le 0 .$$
--
--   This is the Blackwell condition behind the TFRB policy: in the order of the current debts, the expected reward points away from the positive debts.
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - generalization: for j = 1, …, m (the firms with positive debt), in the debt order of period t → for every j ≤ n and every priority list, and in each simulated period on each event {L(t) = σ}; reason: the proof does not use the sign of the debts; the printed claim is the case j ≤ m of the second clause
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), Claim 2, p. A4 (PDF 36); proof pp. A4–A5 (PDF 36–37)

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory

/-- **Claim 2**, Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13), p. A4 (PDF 36). Let `β` be feasible for (8), and `R_i = β_i E[X̂_i] − A_i`.
In the order of a priority list, the expected reward of the first `j` firms is at most `0`, for
every `j`. The first clause is the statement for a fixed list `σ`. The second is the statement in
simulated period `t` given `L(t + 1) = σ` (Lean's period index `t` is the paper's `t + 1`). -/
theorem claim_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Q : Fin n → ℝ) (s : ℝ) (hs : 0 ≤ s) (β : Fin n → ℝ) (hβ : M.IsFeasibleLP Q s β) :
    (∀ (σ : Equiv.Perm (Fin n)) (j : ℕ), j ≤ n →
      ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < j),
        (β (σ l) * M.mean Q (σ l) - ∫ ω, priorityAlloc σ (M.vacVec Q ω) s (σ l) ∂P) ≤ 0) ∧
    (∀ (run : RunData n s) (T t : ℕ), 1 ≤ t → t < T →
      ∀ (σ : Equiv.Perm (Fin n)) (j : ℕ), j ≤ n →
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < j),
          ∫ ξ in {ξ | run.priorityList β (M.mean Q) (extendSample ξ) t = σ},
            (β (σ l) * M.mean Q (σ l) -
              priorityAlloc (run.priorityList β (M.mean Q) (extendSample ξ) t)
                (extendSample ξ t) s (σ l)) ∂sampleLaw (P.map (M.vacVec Q)) T ≤ 0) := by sorry

end OnDemandCoord
