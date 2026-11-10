-- Prove2me | Theorems.Thm_GEPPGrowth_Main_lemma_4_5
-- name    : GEPPGrowth.Main.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:13.469783+00:00
-- url     : https://prove2.me/theorems/c660db3e-9576-4aca-8425-35447d50b1ab
-- title:
--   Lemma 4.5 — Determinant Gaussian comparison on conic events
-- statement:
--   Let $\Sigma$ be a $d\times d$
--   positive-definite matrix, and $E\subseteq\mathbb R^d$ be conic. Then,
--
--   $$
--   \Pr_{y\sim N(0,\Sigma)}(y\in E)\ge\dfrac{1}{\|\Sigma^{-1}\|_2^{d/2}\sqrt{\det(\Sigma)}}\cdot\Pr_{y\sim N(0,I_d)}(y\in E)
--   $$.
--
--   This compares the same conic set under a general covariance and under identity covariance.
--
--   Differences from the source:
--   - encoding: probability of every conic subset → Gaussian outer probability of arbitrary conic sets; reason: retains the full all-set domain without imposing Borel measurability
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Lemma 4.5, printed p.8, PDF p.9

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Lemma 4.5, printed p.8 / PDF p.9. prob is Gaussian outer probability on arbitrary sets; no Borel hypothesis is added. -/
theorem lemma_4_5 (d : ℕ) (S : Mat d) (hS : S.PosDef) (E : Set (Vec d)) (hE : Conic E) :
    (1 / (Real.rpow (GaussianMatrix.specNorm S⁻¹) ((d:ℝ)/2) * Real.sqrt S.det)) *
      prob (normal (1 : Mat d)) E ≤ prob (normal S) E := by sorry

end GEPPGrowth.Main
