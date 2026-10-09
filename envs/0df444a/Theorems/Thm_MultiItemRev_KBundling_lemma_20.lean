-- Prove2me | Theorems.Thm_MultiItemRev_KBundling_lemma_20
-- name    : MultiItemRev.KBundling.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:55.314602+00:00
-- url     : https://prove2.me/theorems/b5353ed5-4918-4036-949d-479eaeebe797
-- title:
--   Lemma 20, p. 37 — Rev(X) ≤ r iff X is stochastically dominated by rV, V an ER valuation
-- statement:
--   **Lemma 20.** Let $X$ be a one-good random valuation with law $\nu$, let $r\ge0$, and let $V$ be an ER valuation. Then
--   $$\mathrm{Rev}(X)\le r\iff X\text{ is stochastically dominated by } rV.$$
--
--   This is Proposition 12 (i) of the paper: the ER good scaled by $r$ is the largest one-good valuation with revenue $r$.
--
--   **Formalization Note** $r\in\mathbb R_+$ (the standing "$r\ge0$" of Proposition 12 (i), p. 22); $rV$ is the image of the ER law under $t\mapsto rt$. At $r=0$ it is the point mass at $0$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 37, Lemma 20 (= Proposition 12 (i), p. 22)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Definitions.Def_MultiItemRev_KSeparate_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KBundling

theorem lemma_20 (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (r : ℝ≥0) :
    MultiItemRev.Decomp.Rev1 ν ≤ (r : ℝ≥0∞) ↔
      MultiItemRev.KSeparate.StochDominated ν (MultiItemRev.KSeparate.erLaw.map (fun t => r * t)) := by sorry

end MultiItemRev.KBundling
