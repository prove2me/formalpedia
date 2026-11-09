-- Prove2me | Theorems.Thm_MinSumFPT_lemma_23
-- name    : MinSumFPT.lemma_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:51.174215+00:00
-- url     : https://prove2.me/theorems/772663f5-fb0b-49fe-9bdf-752c66e05146
-- title:
--   Lemma 23 (corrected: $\le$) — absorbing much smaller clusters
-- statement:
--   Assume the setting of §2.5:
--
--   - $d$ is a pseudometric;
--   - $\sigma$ is a clustering into $k$ nonempty clusters with $\mathrm{cost}(\sigma)\le(1+\varepsilon/(2k))\cdot\mathrm{OPT}$;
--   - $0<\varepsilon<1$;
--   - Hypothesis 1 holds with $\alpha=5$;
--   - $L_i$ are the sets of (27).
--
--   For a cluster $C_i$ let
--
--   $$
--   C'_i=C_i\cup\Big(L_i\cap\bigcup_{j:\ \widehat{|C_j|}<\beta\widehat{|C_i|}}(C_j\cap L_j)\Big).
--   $$
--
--   There are absolute constants $c_0\in(0,1)$ and $c_1\ge1$ such that for all $\beta,\gamma\in(0,c_0(\varepsilon/k)^{c_1}]$ and every $i$,
--
--   $$
--   \mathrm{cost}(C'_i)\ \le\ \mathrm{cost}(C_i)+25\,k^2\,\beta\,\gamma^{-1}\Big(\mathrm{cost}(C_i)+\frac{\varepsilon}{100k}\cdot\mathrm{OPT}\Big).
--   $$
--
--   Points shared with a much smaller cluster can therefore be given to the larger cluster at little cost. This is the local step before the conflict graph is formed.
--
--   Differences from the source:
--   - correction: strict inequality cost(C′_i) < … → ≤; reason: false at n = k = 1: OPT = 0, cost(C₁) = 0, Δ̂ = 0 satisfies (4), C′₁ = C₁, and 0 < 0 fails
--   - reading: 0 < β ≪ 1 and γ = (ε/k)^{O(1)} → ∃ absolute c₀ ∈ (0,1), c₁ ≥ 1 with the statement for all β, γ ∈ (0, c₀(ε/k)^{c₁}]; reason: the page's asymptotic smallness conditions; c₀ makes β, γ small even when ε/k is near 1
--   - reading: the extension 𝒞 of P, "w.h.p. near-optimal" (p.34) → cost(𝒞) ≤ (1 + ε/(2k))·OPT; reason: conclusion (ii) of Theorem 6, which §2.5 assumes
--   - encoding: clusterings into k clusters C_1, …, C_k (divisions by |C_i|) → a surjective labelling σ : Fin n → Fin k; reason: the page divides by |C_i| and |Ĉ_i|; excludes only undefined cases
--   - encoding: L_i of (27) at the time of Lemma 23 → closeSet, the sets before the revision; reason: the revision is defined after the lemma (p.36)
--   - generalization: (A, d) a finite metric space (§2.1, p.7) → every pseudometric d (d(x,x) = 0, d ≥ 0, symmetric, triangle inequality); reason: the goal's input is a semi-metric (footnote 1, p.1); every metric is a pseudometric
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 23, p.35

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumFPT_labCost
import Definitions.Def_MinSumFPT_Hyp1
import Definitions.Def_MinSumFPT_conflictGraph
open scoped Classical

namespace MinSumFPT

/-- Lemma 23 (corrected: ≤) (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 23, p.35): in the setting of §2.5 (a clustering `𝒞` with
`cost(𝒞) ≤ (1 + ε/(2k)) ⋅ OPT` and Hypothesis 1 for α = 5), for a cluster `C_i` let
`C′_i = C_i ∪ (L_i ∩ ⋃_{j : |Ĉ_j| < β|Ĉ_i|} (C_j ∩ L_j))` with the sets `L` of (27). Then
`cost(C′_i) ≤ cost(C_i) + 25 ⋅ k² ⋅ β ⋅ γ⁻¹ ⋅ (cost(C_i) + (ε/(100k)) ⋅ OPT)`.

**Formalization Note.** "β = (ε/k)^{O(1)}" and "γ = (ε/k)^{O(1)}" are read as: there are absolute
constants `c₀ ∈ (0, 1)`, `c₁ ≥ 1` such that the lemma holds for all `β, γ ∈ (0, c₀(ε/k)^{c₁}]`.
𝒞 is a surjective labelling; OPT is `optCost d k`; the sets `L` are those of (27) before the
revision. The page's strict inequality is false at `n = k = 1` (see the Differences). -/
theorem lemma_23 :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ c₀ < 1 ∧ 1 ≤ c₁ ∧
      ∀ (n k : ℕ) (d : Fin n → Fin n → ℝ) (σ : Fin n → Fin k) (ε γ β : ℝ)
        (E : Estimates n k),
        MinSumClust.IsPseudometric d → Function.Surjective σ →
        labCost d σ ≤ (1 + ε / (2 * k)) * optCost d k →
        0 < ε → ε < 1 → 0 < β → β ≤ c₀ * (ε / k) ^ c₁ → 0 < γ → γ ≤ c₀ * (ε / k) ^ c₁ →
        Hyp1 d σ ε 5 γ E →
        ∀ i : Fin k,
          MinSumClust.cost d (clusterOf σ i ∪ (closeSet d ε γ E i ∩
              (Finset.univ.filter (fun j => E.chat j < β * E.chat i)).biUnion
                (fun j => clusterOf σ j ∩ closeSet d ε γ E j))) ≤
            MinSumClust.cost d (clusterOf σ i) +
              25 * (k : ℝ) ^ 2 * β * γ⁻¹ *
                (MinSumClust.cost d (clusterOf σ i) + ε / (100 * k) * optCost d k) := by sorry

end MinSumFPT
