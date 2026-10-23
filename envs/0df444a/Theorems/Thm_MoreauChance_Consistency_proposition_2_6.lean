-- Prove2me | Theorems.Thm_MoreauChance_Consistency_proposition_2_6
-- name    : MoreauChance.Consistency.proposition_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:22.978986+00:00
-- url     : https://prove2.me/theorems/76c5c8ed-9327-4d33-9a5b-249f2f489f24
-- title:
--   Proposition 2.6, p. 8 — ϕ(x) = ℙ(S^h_Φ(x, ξ) ≤ h(x)) (12)
-- statement:
--   Let $\mathcal H$ be a separable Hilbert space, $\mathcal Y$ a Banach space, $\xi:\Omega\to\mathbb R^m$ a random vector on a probability space $(\Omega,\mathbb P)$, and let $\mathcal K$, $\mathcal C$, $h$ and $\Phi$ satisfy the conic setting (9)–(10) of §2.4, with $\mathcal K$ a nonempty closed convex cone. Then the probability function $\varphi(x)=\mathbb P(\Phi(x,\xi)\in-\mathcal K)$ is expressed through the supremum function $S^h_\Phi$ of (11):
--   $$
--   \varphi(x)=\mathbb P\big(\omega\in\Omega: S^h_\Phi(x,\xi(\omega))\le h(x)\big)\quad\text{for all }x\in\mathcal H. \tag{12}
--   $$
--
--   This scalarization is what makes the inner Moreau regularization (13) possible: it replaces the conic constraint by a real inequality whose left-hand side is jointly convex.
--
--   **Formalization Note** The page assumes only that $\mathcal K$ is a nonempty convex cone; the formalization adds that $\mathcal K$ is closed. The proof's first step $\Phi\in-\mathcal K\iff-\Phi\in(\mathcal K^-)^-$ is the bipolar theorem, which returns the closure of $\mathcal K$; without closedness (12) can fail. No continuity of $\Phi$ and no density of $\xi$ is assumed, as on the page.
-- source:
--   van Ackooij, Pérez-Aros, Soto & Vilches, Inner Moreau envelope of nonsmooth conic chance constrained optimization problems, arXiv:2301.09803v1, p. 8, Proposition 2.6, Equation (12)

import Mathlib
import Definitions.Def_MoreauChance_Consistency_Basic
import Definitions.Def_MoreauChance_Consistency_Setting

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace MoreauChance.Consistency

theorem proposition_2_6
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ) :
    ∀ x : H, probFun K Φ μ ξ x =
      μ {ω | supFun C h Φ (WithLp.toLp 2 (x, ξ ω)) ≤ (h x : EReal)} := by sorry

end MoreauChance.Consistency
