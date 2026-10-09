-- Prove2me | Theorems.Thm_MultiItemRev_KSeparate_lemma_20
-- name    : MultiItemRev.KSeparate.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:28:42.236418+00:00
-- url     : https://prove2.me/theorems/d4115083-ec5f-48d4-a636-10d752fce30e
-- title:
--   Lemma 20, p. 37 — equal-revenue domination characterization
-- statement:
--   Let $X$ be a nonnegative one-good valuation, $r\ge0$, and $V$ an equal-revenue valuation with $\Pr[V\ge p]=1/p$ for $p\ge1$. Then
--
--   $$\operatorname{Rev}(X)\le r\quad\Longleftrightarrow\quad X\preceq_{\mathrm{st}}rV.$$
--
--   This identifies the equal-revenue law as an upper comparison law at each prescribed revenue. The case $r=0$ is included.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 37, Lemma 20; p. 22, Proposition 12(i)

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KSeparate

theorem lemma_20 (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (r : ℝ≥0) :
    MultiItemRev.Decomp.Rev1 ν ≤ (r : ℝ≥0∞) ↔
      StochDominated ν (erLaw.map (fun t => r * t)) := by sorry

end MultiItemRev.KSeparate
