-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_BallRatios_maximal_tail
-- name    : OAI.EntropyRateDimension.BallRatios.maximal_tail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:43:07.924232+00:00
-- url     : https://prove2.me/theorems/b12a7b44-8d78-4e74-b790-4b41b5b97ea9
-- title:
--   Tail bound for the maximal ball ratio
-- statement:
--   For measures $\mu,\nu$ on $\mathbb R$, let $M(x)=\sup_q\mu(\bar B(x,q))/\nu(\bar B(x,q))$ over rational radii $0<q\le1$, the log envelope $\max(0,\log M(x))$, and the log ratio $\log\bigl(\mu(\bar B(x,r))/\nu(\bar B(x,r))\bigr)$.
--
--   Let $N$ be a constant with the Besicovitch property: for all $\mu,\nu,t,E$, if every $x\in E$ has a radius $0<r\le1$ with $\nu(\bar B(x,r))\le t\mu(\bar B(x,r))$, then $\nu(E)\le Nt\mu(\mathbb R)$. Then for $\nu$ finite and $0<a<\infty$,
--   $$
--   \nu\{x:M(x)>a\}\le N\,a^{-1}\mu(\mathbb R) .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/BallRatios.lean#L74-L91

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.BallRatios
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

theorem OAI.EntropyRateDimension.BallRatios.maximal_tail {N : ℕ}
    (hN : ∀ (μ ν : Measure ℝ) (t : ℝ≥0∞) (E : Set ℝ),
      (∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ν (closedBall x r) ≤ t*μ (closedBall x r)) →
      ν E ≤ N*t*μ univ)
    (μ ν : Measure ℝ) [IsFiniteMeasure ν] (a : ℝ≥0∞) (ha : a ≠ 0) (hat : a ≠ ⊤) :
    ν {x | a < maximal μ ν x} ≤ N * a⁻¹ * μ univ := by sorry
