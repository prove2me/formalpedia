-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_Supplement_lemma_5_1
-- name    : InducedExpanderTest989.Structural.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:30:49.253833+00:00
-- url     : https://prove2.me/theorems/42efec2d-e945-4cea-b056-0dbf5454508a
-- title:
--   Lemma 5.1 — adding vertices to an induced expander by subdivision
-- statement:
--   Let $G$ be a simple graph on $V=[n]$ of maximum degree at most $d\ge2$, with inner conductance $\Phi_{\rm in}$ normalized by $d$. Let $U\subseteq V$ have $m=|U|\ge2$ vertices with $\Phi_{\rm in}(G[U])\ge\theta>0$, and let $W\subseteq V\setminus U$ have $b\le m-1$ vertices. Then there is a simple graph $G'$ on $V$ of maximum degree at most $d$ with
--   $$|E(G)\triangle E(G')|\le (d+3)\,b\qquad\text{and}\qquad \Phi_{\rm in}\big(G'[U\cup W]\big)\ge\frac{\theta}{2d+2}.$$
--
--   The lemma enlarges an expanding core by any number of outside vertices smaller than its size, at an edit cost linear in the number of added vertices and a conductance loss depending only on $d$. It is the repair step behind Corollary 5.1.
--
--   **Formalization Note** $\Phi_{\rm in}(G[U])$ is the mission's `innerConductance d G U`; the bound $b\le m-1$ is written $|W|+1\le|U|$. The bound $\theta\le1$ used in the source's proof follows from the degree bound and is not a hypothesis.
--
--   Differences from the source:
--   - encoding: b ≤ m − 1 → W.card + 1 ≤ U.card; reason: the same condition on natural numbers, without truncated subtraction
--   - encoding: |E(G)△E(G′)| → editDistance G G′, the ncard of the symmetric difference of the edge sets; reason: Lean convention for the same count
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.32 (PDF p.34), Lemma 5.1

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Graph
import Definitions.Def_InducedExpanderTest989_Structural_Supplement_Distance

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural.Supplement

/-- Peng–Shen, STOC 2027 #989, Lemma 5.1 (p. 32, PDF 34). -/
theorem lemma_5_1 {n : ℕ} (d : ℕ) (hd : 2 ≤ d) (G : SimpleGraph (Fin n)) (hG : DegreeBound d G)
    (U W : Finset (Fin n)) (hU : 2 ≤ U.card) (hUW : Disjoint U W) (hb : W.card + 1 ≤ U.card)
    (θ : ℝ) (hθ : 0 < θ) (hΦ : θ ≤ innerConductance d G U) :
    ∃ G' : SimpleGraph (Fin n), DegreeBound d G' ∧
      editDistance G G' ≤ (d + 3) * W.card ∧
      θ / (2 * d + 2) ≤ innerConductance d G' (U ∪ W) := by sorry

end InducedExpanderTest989.Structural.Supplement
