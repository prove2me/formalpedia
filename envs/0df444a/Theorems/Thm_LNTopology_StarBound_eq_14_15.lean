-- Prove2me | Theorems.Thm_LNTopology_StarBound_eq_14_15
-- name    : LNTopology.StarBound.eq_14_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:19.511898+00:00
-- url     : https://prove2.me/theorems/9efbfee3-da16-48bd-8401-64a8cc805877
-- title:
--   (14)–(15), p. 14 — every supporting network costs at least $\sum_{f_i>0}c(f_i)$ and at least $\sum_{f_i<0}c(f_i)$
-- statement:
--   Let $V$ be a finite set of nodes, $c$ a channel cost function satisfying (MO), (SY), (CI) and (SA), and $\mathcal F=(f_i)_{i\in V}$ a payment flow. Let $G=(\lambda_{i,j})$ be any Lightning Network on $V$ (anti-symmetric) that supports $\mathcal F$. Then
--   $$c(G)\;\ge\;\sum_{i:\,f_i>0}c(f_i)\qquad\text{and}\qquad c(G)\;\ge\;\sum_{i:\,f_i<0}c(f_i).$$
--
--   These are the inequalities (14) and (15) of the paper, and they give the lower bound $c_{\min}(\mathcal F)\ge\max\big(\sum_{f_i>0}c(f_i),\sum_{f_i<0}c(f_i)\big)$ of Theorem 3.10.
--
--   **Formalization Note.** The paper derives (14)–(15) for a cost-minimizing network, which by Theorem 3.1 has channels only between nodes of opposite flow signs, and it assumes such a minimizer exists. The statement here is for *every* supporting Lightning Network; it is the form the infimum $c_{\min}$ needs, since the minimum need not be attained when $c$ is not continuous. This is a generalization of the displayed inequalities, not a restatement. (SA) is in its corrected form, for all $x,y>0$. Under the row-sum sign convention a positive $f_i$ is a net payer; the statement is symmetric under $\mathcal F\mapsto-\mathcal F$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 14 (PDF 15), App. C, proof of Theorem 3.10, (14) and (15)

import Mathlib
import Definitions.Def_LNTopology_StarBound_Model

namespace LNTopology.StarBound

/-- (14)–(15), proof of Theorem 3.10, p. 14, for every supporting network: the cost of any
Lightning Network supporting `f` is at least the total cost of the positive flows and at least
the total cost of the negative flows. -/
theorem eq_14_15 {V : Type*} [Fintype V] (c : ℝ → ℝ) (hc : IsChannelCost c) (f : V → ℝ)
    (Λ : V → V → ℝ) (hLN : IsLN Λ) (hΛ : Supports Λ f) :
    ∑ i ∈ Finset.univ.filter (fun i => 0 < f i), c (f i) ≤ cost c Λ ∧
      ∑ i ∈ Finset.univ.filter (fun i => f i < 0), c (f i) ≤ cost c Λ := by sorry

end LNTopology.StarBound
