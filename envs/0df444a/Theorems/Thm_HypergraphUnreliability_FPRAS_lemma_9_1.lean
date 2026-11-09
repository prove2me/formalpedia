-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_lemma_9_1
-- name    : HypergraphUnreliability.FPRAS.lemma_9_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:59.33101+00:00
-- url     : https://prove2.me/theorems/9c26aceb-c078-4460-ab58-b3eaea7d946b
-- title:
--   Lemma 9.1 — Product-measure relative stability
-- statement:
--   Let $A$ be an increasing event in independent failed-edge indicators, on a finite label set. Let $p_e,q_e\in[0,1]$ and $t_e\ge0$ satisfy $e^{-t_e}p_e\le q_e\le e^{t_e}p_e$ for every label $e$. Then
--   $$e^{-\sum_e t_e}\,P_p(A)\le P_q(A)\le e^{\sum_e t_e}\,P_p(A).$$
--
--   This compares unreliability under the failure probabilities of the input and under their rounded versions, and it gives relative accuracy however small the event's probability is.
--
--   Differences from the source: none.
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Lemma 9.1, p. 12

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Hypergraph

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

open LabeledHypergraph

/-- Lemma 9.1, p. 12 (product-measure relative stability). -/
theorem lemma_9_1 {E : Type} [Fintype E] (A : Finset E → Prop) (hA : IsIncreasing A)
    (p q t : E → ℝ) (hp : ∀ e, p e ∈ Set.Icc (0 : ℝ) 1) (hq : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1)
    (ht : ∀ e, 0 ≤ t e)
    (hlow : ∀ e, Real.exp (-t e) * p e ≤ q e) (hupp : ∀ e, q e ≤ Real.exp (t e) * p e) :
    Real.exp (-∑ e, t e) * prodProb p A ≤ prodProb q A ∧
      prodProb q A ≤ Real.exp (∑ e, t e) * prodProb p A := by sorry

end HypergraphUnreliability.FPRAS
