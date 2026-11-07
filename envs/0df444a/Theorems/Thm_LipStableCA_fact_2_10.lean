-- Prove2me | Theorems.Thm_LipStableCA_fact_2_10
-- name    : LipStableCA.fact_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:50:02.7679+00:00
-- url     : https://prove2.me/theorems/c93b4963-98a9-44d3-b908-12b51d3446ea
-- title:
--   Fact 2.10 — MIDR rules with VCG-type expected payments are truthful in expectation
-- statement:
--   Let $(S,p)$ be a randomized mechanism whose allocation rule is maximal in distributional range with range $D$, a report-independent set of distributions on allocations. Suppose that for every bidder $i$ and profile $v\in\mathcal V^n$,
--   $$\mathbb E[p_i(v)]=\max_{\lambda\in D}\mathbb E_{S\sim\lambda}\Bigl[\sum_{h\ne i}v_h(S_h)\Bigr]-\mathbb E\Bigl[\sum_{h\ne i}v_h(S(v)_h)\Bigr],$$
--   where the payment may be random and may depend on the realized allocation. Then $(S,p)$ is truthful in expectation, and $0\le\mathbb E[p_i(v)]\le\mathbb E[v_i(S(v)_i)]$.
--
--   This is the tool behind the truthfulness of the random discount auction.
--
--   **Formalization Note.** The printed maximum is a hypothesis that it is attained, and valuations in $\mathcal V$ are automatically nonnegative.
--
--   Differences from the source:
--   - encoding: $\max_{\lambda\in D}$ as printed → the hypothesis that the supremum over $D$ is attained (`IsGreatest`), part of the printed formula; reason: the printed formula presupposes the maximum; `sSup` would be $0$ on an unbounded set
--   - encoding: the expectation $\mathbb E[p_i(v)]$ → integrability of the payments as a hypothesis; reason: a non-integrable payment has no expectation; the Bochner integral would return $0$
--   - encoding: the paper does not name a σ-algebra on the seed space → measurability of the rule stated as a clause or a hypothesis; reason: this is what makes the allocation law meaningful (paper.md decision 3)
--   - encoding: distributions on $\mathcal A$ → real mass functions (`IsLaw`); reason: $\mathcal A$ is finite; same objects
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Fact 2.10, p.9

import Definitions.Def_LipStableCA_Mechanism
import Definitions.Def_LipStableCA_IsMIDR
open MeasureTheory

namespace LipStableCA

/-- **Fact 2.10.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.9. **Formalization Note.** the hypothesis that the supremum over `D` is attained (`IsGreatest`), part of the printed formula: the printed formula presupposes the maximum; `sSup` would be `0` on an unbounded set. integrability of the payments as a hypothesis: a non-integrable payment has no expectation; the Bochner integral would return `0`. measurability of the rule stated as a clause or a hypothesis: this is what makes the allocation law meaningful (paper.md decision 3). real mass functions (`IsLaw`): `A` is finite; same objects. -/
theorem fact_2_10 {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Mechanism n m Ω) (hM : M.Measurable) (D : Set (Alloc n m → ℝ)) (hD : ∀ l ∈ D, IsLaw l)
    (hMIDR : IsMIDR (M.law μ) D)
    (hint : ∀ v, IsProfile v → ∀ i, Integrable (fun ω => M.pay v ω i) μ)
    (hpay : ∀ (i : Fin n) (v : Profile n m), IsProfile v → ∃ x, IsGreatest (othersWelfare v i '' D) x ∧
      ∫ ω, M.pay v ω i ∂μ = x - othersWelfare v i (M.law μ v)) :
    M.IsTIE μ ∧ ∀ (i : Fin n) (v : Profile n m), IsProfile v →
      0 ≤ ∫ ω, M.pay v ω i ∂μ ∧ ∫ ω, M.pay v ω i ∂μ ≤ ∫ ω, v i ((M.alloc v ω).1 i) ∂μ := by sorry

end LipStableCA
