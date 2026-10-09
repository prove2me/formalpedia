-- Prove2me | Theorems.Thm_MKVDPP_Weak_corollary_4_6
-- name    : MKVDPP.Weak.corollary_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:29:29.913982+00:00
-- url     : https://prove2.me/theorems/5fc05d56-c058-4e71-8ed8-372b00b5bd2e
-- title:
--   Corollary 4.6, p. 18 — V_W(t,ν) = sup over weak control rules ℙ̄ ∈ 𝒫̄_W(t,ν) of J(t,ℙ̄)
-- statement:
--   Under the standing assumptions, for every $(t,\nu)\in[0,T]\times\mathcal P(\mathcal C^n)$,
--   $$V_W(t,\nu)=\sup_{\bar{\mathbb P}\in\bar{\mathcal P}_W(t,\nu)}J(t,\bar{\mathbb P}),\qquad J(t,\bar{\mathbb P}):=\mathbb E^{\bar{\mathbb P}}\Big[\int_t^TL(s,X,\bar\mu_s,\bar\alpha_s)\,ds+g(X,\mu_T)\Big].\qquad(4.9)$$
--
--   The value of the weak problem is therefore the supremum of a functional over a set of probability measures on the canonical space $\bar\Omega$.
--
--   **Formalization Note** Only the first display of the corollary is stated; the strong-formulation displays belong to the companion mission. $\sup\emptyset=-\infty$ on both sides.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 18, Corollary 4.6 (first display), (4.9)

import Mathlib
import Definitions.Def_MKVDPP_Weak_Setting
import Definitions.Def_MKVDPP_Weak_WeakControl
import Definitions.Def_MKVDPP_Weak_Canonical

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MKVDPP.Weak

/-- **Corollary 4.6** (p. 18, first display). The weak value function equals the supremum of the
canonical reward over weak control rules: `V_W(t,ν) = sup_{ℙ̄ ∈ 𝒫̄_W(t,ν)} J(t, ℙ̄)` (4.9). -/
theorem corollary_4_6
    {T : ℝ≥0} (hT : 0 < T) {n d ℓ : ℕ} {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U] [MeasurableSpace U] [BorelSpace U]
    (u₀ : U) (p : ℝ) (hp : 0 ≤ p) (π : U → ℝ) (hπ : IsControlEncoding π)
    (c : Coeffs T n d ℓ U) (hc : c.IsAdmissible)
    (t : ℝ≥0) (ht : t ≤ T) (ν : ProbabilityMeasure (Cpath T n)) :
    VW c u₀ p π t ν = ⨆ P ∈ PbarW hπ c u₀ p t ν, Jbar hπ c u₀ t P := by sorry

end MKVDPP.Weak
