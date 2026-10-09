-- Prove2me | Theorems.Thm_MKVDPP_BStrong_lemma_4_4_ii
-- name    : MKVDPP.BStrong.lemma_4_4_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:26:34.701469+00:00
-- url     : https://prove2.me/theorems/09a8e6fe-621b-43b1-b9e4-0ebf5050bba7
-- title:
--   Lemma 4.4(ii), forward clause — strong controls induce canonical rules
-- statement:
--   For $t\in[0,T]$, $\nu\in\mathcal P_2(\mathcal C^n)$ and Assumption 2.8, every strong control induces a strong canonical rule, and every $\mathbb B$ strong control induces a $\mathbb B$ strong canonical rule. In both cases the induced probability is the image law
--
--   $$\bar P^\gamma=\mathbb P^\gamma\circ(X^\gamma,A^\gamma,W^\gamma,B^\gamma,\hat\mu^\gamma)^{-1}.$$
--
--   This is the forward part of equation (4.8), identifying the original controls with admissible canonical rules.
--
--   **Formalization Note** The printed converse is omitted because Definition 4.1 leaves the canonical $A$ path before $t$ unconstrained, while every induced control has $A_s=0$ there. A converse requires that normalization.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 17, Lemma 4.4(ii), forward clause of (4.8)

import Definitions.Def_MKVDPP_BStrong_Canonical

open MeasureTheory ProbabilityTheory Filter Classical
open scoped ENNReal NNReal Topology BigOperators

namespace MKVDPP.BStrong

/-- Lemma 4.4(ii), p. 17, the forward strong-control clauses of (4.8).
The printed converse needs a pre-t normalization of the canonical A path. -/
theorem lemma_4_4_ii {T : ℝ≥0} (hT : 0 < T) {n d ell : ℕ}
    {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U]
    [MeasurableSpace U] [BorelSpace U]
    (M : Model T n d ell U) (hA : Assumption28 T n d ell M.u₀ M.b M.σ M.σ₀)
    (t : ℝ≥0) (ht : t ≤ T) (ν : ProbabilityMeasure (Cpath T n))
    (hν : IsP2 ν) :
    (∀ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∀ γ : WeakControl M Ω t ν, IsStrong γ →
        ∃ Pbar : ProbabilityMeasure (OmegaBar T n d ell),
          Pbar ∈ PbarS M t ht ν ∧ InducedBy γ Pbar) ∧
    (∀ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∀ γ : WeakControl M Ω t ν, IsBStrong γ →
        ∃ Pbar : ProbabilityMeasure (OmegaBar T n d ell),
          Pbar ∈ PbarSB M t ht ν ∧ InducedBy γ Pbar) := by sorry

end MKVDPP.BStrong
