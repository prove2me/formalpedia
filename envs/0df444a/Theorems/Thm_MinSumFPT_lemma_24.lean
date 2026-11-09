-- Prove2me | Theorems.Thm_MinSumFPT_lemma_24
-- name    : MinSumFPT.lemma_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:21.854567+00:00
-- url     : https://prove2.me/theorems/1fff3060-71b0-4891-baed-6e765c5be6c1
-- title:
--   Lemma 24 — clusters in one component of $K$ have comparable sizes and nearby centers
-- statement:
--   Assume the setting of Lemma 23 with $\beta=\varepsilon\gamma/(100k^3)$, the revised sets $L_i$ and the conflict graph $K$. There are absolute constants $c_0\in(0,1)$ and $c_1\ge1$ such that for all $\gamma\in(0,c_0(\varepsilon/k)^{c_1}]$ and all clusters $i,j$ in one connected component of $K$:
--
--   $$
--   \widehat{|C_i|}\le\beta^{-k+1}\cdot\widehat{|C_j|},
--   \qquad
--   d(\hat\mu_{C_i},\hat\mu_{C_j})\le7\cdot\gamma^{-1}\cdot\beta^{-4k+6}\cdot\frac{\widehat{\mathrm{OPT}}}{\big(\max\{\widehat{|C_i|},\widehat{|C_j|}\}\big)^2}.
--   $$
--
--   Within a component, all clusters have sizes within a factor $\beta^{-k+1}$ of each other and their centers lie close together. This makes the MAX $h$-CUT instance of the component dense enough for the sublinear scheme of Theorem 25.
--
--   Differences from the source:
--   - reading: 0 < β ≪ 1 and γ = (ε/k)^{O(1)} → ∃ absolute c₀ ∈ (0,1), c₁ ≥ 1 with the statement for all γ ∈ (0, c₀(ε/k)^{c₁}] (β = εγ/(100k³) as on p.36); reason: the page's asymptotic smallness conditions; c₀ makes β, γ small even when ε/k is near 1
--   - reading: the extension 𝒞 of P, "w.h.p. near-optimal" (p.34) → cost(𝒞) ≤ (1 + ε/(2k))·OPT; reason: conclusion (ii) of Theorem 6, which §2.5 assumes
--   - encoding: clusterings into k clusters C_1, …, C_k (divisions by |C_i|) → a surjective labelling σ : Fin n → Fin k; reason: the page divides by |C_i| and |Ĉ_i|; excludes only undefined cases
--   - encoding: i, j in one connected component K′ of K → K.Reachable i j; reason: the same relation
--   - generalization: (A, d) a finite metric space (§2.1, p.7) → every pseudometric d (d(x,x) = 0, d ≥ 0, symmetric, triangle inequality); reason: the goal's input is a semi-metric (footnote 1, p.1); every metric is a pseudometric
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 24, p.36

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumFPT_labCost
import Definitions.Def_MinSumFPT_Hyp1
import Definitions.Def_MinSumFPT_conflictGraph

namespace MinSumFPT

/-- Lemma 24 (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 24, p.36): in the setting of §2.5 with `β = ε ⋅ γ/(100k³)`, after the
revision of the sets `L_i`, let `i, j` be two clusters in one connected component of the conflict
graph `K`. Then `|Ĉ_i| ≤ β^{−k+1} ⋅ |Ĉ_j|` and
`d(µ̂_{C_i}, µ̂_{C_j}) ≤ 7 ⋅ γ⁻¹ ⋅ β^{−4k+6} ⋅ ÔPT/(max{|Ĉ_i|, |Ĉ_j|})²`.

**Formalization Note.** "γ = (ε/k)^{O(1)}" is read as: there are absolute constants `c₀ ∈ (0, 1)`,
`c₁ ≥ 1` such that the lemma holds for all `γ ∈ (0, c₀(ε/k)^{c₁}]`. 𝒞 is a surjective labelling with
`cost(𝒞) ≤ (1 + ε/(2k)) ⋅ OPT` and Hypothesis 1 for α = 5; "in one connected component" is
`K.Reachable i j`. -/
theorem lemma_24 :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ c₀ < 1 ∧ 1 ≤ c₁ ∧
      ∀ (n k : ℕ) (d : Fin n → Fin n → ℝ) (σ : Fin n → Fin k) (ε γ β : ℝ)
        (E : Estimates n k),
        MinSumClust.IsPseudometric d → Function.Surjective σ →
        labCost d σ ≤ (1 + ε / (2 * k)) * optCost d k →
        0 < ε → ε < 1 → 0 < γ → γ ≤ c₀ * (ε / k) ^ c₁ → β = ε * γ / (100 * (k : ℝ) ^ 3) →
        Hyp1 d σ ε 5 γ E →
        ∀ i j : Fin k, (conflictGraph d ε γ β E).Reachable i j →
          E.chat i ≤ β⁻¹ ^ (k - 1) * E.chat j ∧
            d (E.muHat i) (E.muHat j) ≤
              7 * γ⁻¹ * β ^ (-4 * (k : ℤ) + 6) * (E.optHat / (max (E.chat i) (E.chat j)) ^ 2) := by sorry

end MinSumFPT
