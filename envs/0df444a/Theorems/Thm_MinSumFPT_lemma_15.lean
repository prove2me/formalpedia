-- Prove2me | Theorems.Thm_MinSumFPT_lemma_15
-- name    : MinSumFPT.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:09.581424+00:00
-- url     : https://prove2.me/theorems/fb7001e0-ce52-446a-9a50-a0dc06801725
-- title:
--   Lemma 15 (corrected: labels $\mathrm{mid}_s$ for every $s$) — $\mathrm{cost}(\mathcal C')\le(1+44k^2\beta+14\beta^2/\gamma+5\gamma)\cdot\mathrm{OPT}$
-- statement:
--   Assume the setting of Lemma 13. Fix any valid choice of the $j_p$, any $\gamma^2$-approximations $\hat n_{h,i}$ of $|B^h\cap D_i|$, any optimal capacitated assignment $f$ and any admissible completion $l$, and let $\mathcal C'$ be the clustering they produce. There are absolute constants $c_0\in(0,1)$ and $c_1\ge1$ such that for all $\beta,\gamma\in(0,c_0(\varepsilon/k)^{c_1}]$,
--
--   $$
--   \mathrm{cost}(\mathcal C')\ \le\ \Big(1+44k^2\beta+\frac{14\beta^2}{\gamma}+5\gamma\Big)\cdot\mathrm{OPT}.
--   $$
--
--   $\mathcal C'$ extends the partial clustering that Stage 2 returns. Lemma 15 is the cost guarantee behind Theorem 6: the far points can be committed according to the flow solution $f$ at a cost of $(1+O(\varepsilon/k))\cdot\mathrm{OPT}$.
--
--   Differences from the source:
--   - correction: labels L = {0, 1, …, k, cls, mid₁, …, mid_R, far} → labels with mid_s for every s ∈ ℕ; reason: with R = ⌊5 log_{1+γ}(1/β)⌋ a point of C_i^mid can need s = R + 1 (γ = 1, β = 1/3: R = 7, (1+γ)^R = 128 < 243 = β⁻⁵), where the printed h_p is undefined; empty buckets carry no constraint
--   - reading: 0 < β ≪ 1 and γ = (ε/k)^{O(1)} → ∃ absolute c₀ ∈ (0,1), c₁ ≥ 1 with the statement for all β, γ ∈ (0, c₀(ε/k)^{c₁}]; reason: the page's asymptotic smallness conditions; c₀ makes β, γ small even when ε/k is near 1
--   - encoding: clusterings into k clusters C_1, …, C_k (divisions by |C_i|) → a surjective labelling σ : Fin n → Fin k; reason: the page divides by |C_i| and |Ĉ_i|; excludes only undefined cases
--   - encoding: d_p(j) = ∞ and an optimal assignment → a constraint excluding the infinite-cost pairs; f minimizes the finite cost among feasible assignments; reason: the assignment induced by 𝒟 is feasible of finite cost (p.22), so the optimum is finite
--   - encoding: j_p an arg min, g arbitrary, f an optimal assignment, l an assignment respecting the capacities → for every valid j_p, g, f and l; reason: the page's choices are arbitrary; the lemma holds for each
--   - generalization: (A, d) a finite metric space (§2.1, p.7) → every pseudometric d (d(x,x) = 0, d ≥ 0, symmetric, triangle inequality); reason: the goal's input is a semi-metric (footnote 1, p.1); every metric is a pseudometric
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 15, p.24

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumFPT_labCost
import Definitions.Def_MinSumFPT_Hyp1
import Definitions.Def_MinSumFPT_labD
import Definitions.Def_MinSumFPT_labCprime

namespace MinSumFPT

/-- Lemma 15 (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 15, p.24): in the setting of §2.4, the clustering `𝒞′` satisfies
`cost(𝒞′) ≤ (1 + 44k²β + 14β²/γ + 5γ) ⋅ OPT`.

**Formalization Note.** The setting is that of Lemma 13 (optimal surjective `𝒞`, Hypothesis 1 with
α = 5, any redirection map `g`, `β, γ ∈ (0, c₀(ε/k)^{c₁}]`), plus any valid choice of the `j_p`, any
γ²-approximations `n̂_{h,i}` of `|B^h ∩ D_i|`, any optimal capacitated assignment `f` and any
admissible completion `l`; 𝒞′ is `labCprime`. The label set contains every `mid_s` (the printed
set stops at `mid_R`, see the Differences). -/
theorem lemma_15 :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ c₀ < 1 ∧ 1 ≤ c₁ ∧
      ∀ (n k : ℕ) (d : Fin n → Fin n → ℝ) (σ : Fin n → Fin k) (ε γ β : ℝ)
        (E : Estimates n k) (g : Fin n → Fin k) (jp : Fin n → Option (Fin k))
        (nhat : (Fin k → Label k) → Fin k → ℝ) (f l : Fin n → Fin k),
        MinSumClust.IsPseudometric d → Function.Surjective σ → labCost d σ = optCost d k →
        0 < ε → ε < 1 → 0 < β → β ≤ c₀ * (ε / k) ^ c₁ → 0 < γ → γ ≤ c₀ * (ε / k) ^ c₁ →
        Hyp1 d σ ε 5 γ E → IsRedirection d ε γ β E σ g → IsJChoice d ε γ β E jp →
        IsCapEstimate d ε γ β E σ g jp nhat → IsOptimalAssign d ε γ β E jp nhat f →
        IsAdmissibleCompletion d ε γ β E σ g jp nhat f l →
        labCost d (labCprime d ε γ β E σ g f l) ≤
          (1 + 44 * (k : ℝ) ^ 2 * β + 14 * β ^ 2 / γ + 5 * γ) * optCost d k := by sorry

end MinSumFPT
