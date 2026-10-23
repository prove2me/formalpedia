-- Prove2me | Theorems.Thm_MoreauChance_Consistency_proposition_5_1
-- name    : MoreauChance.Consistency.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:56.045986+00:00
-- url     : https://prove2.me/theorems/b0637b73-0ad4-4a4d-bd23-80be062c1806
-- title:
--   Proposition 5.1, p. 19 — Mλ(p) → M(p) in the Painlevé–Kuratowski sense, and in the Mosco sense if h is weakly continuous
-- statement:
--   In the setting of Theorem 3.1 (separable Hilbert $\mathcal H$, Banach $\mathcal Y$, $\xi$ with a Lebesgue density, conic setting (9)–(10) with $\mathcal K$ closed, $\Phi$ continuous), fix $p\in[0,1]$ and let $M(p)=\{x:\varphi(x)\ge p\}$, $M_\lambda(p)=\{x:\varphi_\lambda(x)\ge p\}$. Then for every sequence of positive numbers $\lambda_k\to0$:
--
--   1. the sets $M_{\lambda_k}(p)$ Painlevé–Kuratowski converge to $M(p)$;
--   2. if the function $h$ of (10) is sequentially weakly continuous, the sets $M_{\lambda_k}(p)$ Mosco converge to $M(p)$.
--
--   This is the convergence of feasible sets on which the consistency of the regularized problems (Theorem 5.4) rests.
--
--   **Formalization Note** The page writes "the sets $M_\lambda(p)$ converge to $M(p)$" as $\lambda\to0$; the formalization states it along every positive sequence $\lambda_k\to0$, which is the form the proof and Theorem 5.4 use.
-- source:
--   van Ackooij, Pérez-Aros, Soto & Vilches, Inner Moreau envelope of nonsmooth conic chance constrained optimization problems, arXiv:2301.09803v1, p. 19, Proposition 5.1

import Mathlib
import Definitions.Def_MoreauChance_Consistency_Basic
import Definitions.Def_MoreauChance_Consistency_Setting

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace MoreauChance.Consistency

theorem proposition_5_1
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hdens : Measure.map ξ μ ≪ volume)
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (hset : IsConicSetting K C h Φ)
    (hΦ : Continuous (fun q : H × EuclideanSpace ℝ (Fin m) => Φ q.1 q.2))
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (lamk : ℕ → ℝ) (hlam_pos : ∀ k, 0 < lamk k) (hlam_lim : Tendsto lamk atTop (𝓝 0)) :
    PKConv (fun k => feasSetReg C h Φ μ ξ (lamk k) p) (feasSet K Φ μ ξ p) ∧
      (SeqWeakCont h →
        MoscoConv (fun k => feasSetReg C h Φ μ ξ (lamk k) p) (feasSet K Φ μ ξ p)) := by sorry

end MoreauChance.Consistency
