-- Prove2me | Theorems.Thm_MinSumFPT_lemma_13
-- name    : MinSumFPT.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:20:09.38337+00:00
-- url     : https://prove2.me/theorems/6be8045a-ce0a-4f5d-ab22-981065cdd813
-- title:
--   Lemma 13 (corrected: $\le$) — the clustering $\mathcal D$ is near-optimal
-- statement:
--   Assume the setting of §2.4:
--
--   - $d$ is a pseudometric;
--   - $\sigma$ is an optimal clustering into $k$ nonempty clusters, so $\mathrm{cost}(\sigma)=\mathrm{OPT}$;
--   - $0<\varepsilon<1$;
--   - Hypothesis 1 holds with $\alpha=5$;
--   - $g$ is any redirection map, and $\mathcal D$ is the resulting clustering.
--
--   There are absolute constants $c_0\in(0,1)$ and $c_1\ge1$ such that for all $\beta,\gamma\in(0,c_0(\varepsilon/k)^{c_1}]$ and every $i$:
--
--   1. $\mathrm{cost}(D_i)\le\mathrm{cost}(C_i)+36\,(k-1)\,\beta\cdot\mathrm{OPT}$;
--   2. $\mathrm{cost}(C_i^{\neg\mathrm{far}}\cap D_i)\le\mathrm{cost}(C_i^{\neg\mathrm{far}}\cap C_i)+36\,(k-1)\,\beta\cdot\mathrm{OPT}$,
--
--   where $C_i^{\neg\mathrm{far}}=A\setminus C_i^{\mathrm{far}}$.
--
--   Moving the redirected points to their target clusters costs only $O(k\beta)\cdot\mathrm{OPT}$, so $\mathcal D$ can serve as the baseline for the assignment of far points in Lemma 15.
--
--   Differences from the source:
--   - correction: strict inequalities cost(D_i) < … and cost(C_i^{¬far} ∩ D_i) < … → ≤; reason: false at k = 1: C₁^↦ = ∅, D₁ = C₁ and the extra term is 36·0·β·OPT = 0 (proved in the sanity file)
--   - reading: 0 < β ≪ 1 and γ = (ε/k)^{O(1)} → ∃ absolute c₀ ∈ (0,1), c₁ ≥ 1 with the statement for all β, γ ∈ (0, c₀(ε/k)^{c₁}]; reason: the page's asymptotic smallness conditions; c₀ makes β, γ small even when ε/k is near 1
--   - encoding: clusterings into k clusters C_1, …, C_k (divisions by |C_i|) → a surjective labelling σ : Fin n → Fin k; reason: the page divides by |C_i| and |Ĉ_i|; excludes only undefined cases
--   - encoding: g an arbitrary target cluster for each redirected point; D_i = (C_i ∖ C_i^↦) ∪ C_{i↦} → any g with IsRedirection; 𝒟 as the labelling labD; reason: the lemma holds for every choice
--   - generalization: (A, d) a finite metric space (§2.1, p.7) → every pseudometric d (d(x,x) = 0, d ≥ 0, symmetric, triangle inequality); reason: the goal's input is a semi-metric (footnote 1, p.1); every metric is a pseudometric
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 13, p.21

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumFPT_labCost
import Definitions.Def_MinSumFPT_Hyp1
import Definitions.Def_MinSumFPT_labD

namespace MinSumFPT

/-- Lemma 13 (corrected: ≤) (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 13, p.21): in the setting of §2.4 (an optimal clustering
`𝒞` with Hypothesis 1 for α = 5, the clustering `𝒟` built with any redirection map `g`), for every
`i`:
1. `cost(D_i) ≤ cost(C_i) + 36 ⋅ (k − 1) ⋅ β ⋅ OPT`;
2. `cost(C_i^{¬far} ∩ D_i) ≤ cost(C_i^{¬far} ∩ C_i) + 36 ⋅ (k − 1) ⋅ β ⋅ OPT`.

**Formalization Note.** "0 < β ≪ 1" and "γ = (ε/k)^{O(1)}" are read as: there are absolute
constants `c₀ ∈ (0, 1)`, `c₁ ≥ 1` such that the lemma holds for all `β, γ ∈ (0, c₀(ε/k)^{c₁}]`.
𝒞 is a surjective labelling (k nonempty clusters) of cost OPT = `optCost d k`;
`C_i^{¬far} = A ∖ C_i^far`. The page's strict inequalities are false at `k = 1` (see the
Differences). -/
theorem lemma_13 :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ c₀ < 1 ∧ 1 ≤ c₁ ∧
      ∀ (n k : ℕ) (d : Fin n → Fin n → ℝ) (σ : Fin n → Fin k) (ε γ β : ℝ)
        (E : Estimates n k) (g : Fin n → Fin k),
        MinSumClust.IsPseudometric d → Function.Surjective σ → labCost d σ = optCost d k →
        0 < ε → ε < 1 → 0 < β → β ≤ c₀ * (ε / k) ^ c₁ → 0 < γ → γ ≤ c₀ * (ε / k) ^ c₁ →
        Hyp1 d σ ε 5 γ E → IsRedirection d ε γ β E σ g →
        ∀ i : Fin k,
          MinSumClust.cost d (clusterOf (labD d ε γ β E σ g) i) ≤
              MinSumClust.cost d (clusterOf σ i) + 36 * ((k : ℝ) - 1) * β * optCost d k ∧
            MinSumClust.cost d
                ((Finset.univ \ farSet d ε γ β E i) ∩ clusterOf (labD d ε γ β E σ g) i) ≤
              MinSumClust.cost d ((Finset.univ \ farSet d ε γ β E i) ∩ clusterOf σ i) +
                36 * ((k : ℝ) - 1) * β * optCost d k := by sorry

end MinSumFPT
