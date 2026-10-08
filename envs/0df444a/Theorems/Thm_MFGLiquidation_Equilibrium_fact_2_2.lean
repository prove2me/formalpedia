-- Prove2me | Theorems.Thm_MFGLiquidation_Equilibrium_fact_2_2
-- name    : MFGLiquidation.Equilibrium.fact_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:37.450129+00:00
-- url     : https://prove2.me/theorems/015d8abc-4be1-49b0-a776-034acf7656de
-- title:
--   Fact 2.2 — ℋ_l ⊂ ℋ_{l−1} with ‖·‖_{ℋ_{l−1}} ≤ T‖·‖_{ℋ_l}, K_T = 0 for K ∈ ℋ_l (l > 0), ℳ_{−1}·ℋ_l ⊂ ℋ_{l−1}, and the ℳ_l inclusion
-- statement:
--   Let $T>0$, let $\mathbb G$ be a filtration and $l\in\mathbb R$, and let $\mathcal H_l$, $\mathcal M_l$ be the weighted spaces of Definition 2.1. Then:
--
--   1. $\mathcal H_l\subset\mathcal H_{l-1}$ and $\|Y\|_{\mathcal H_{l-1}}\le T\,\|Y\|_{\mathcal H_l}$ (stated for squared norms, $\|Y\|^2_{\mathcal H_{l-1}}\le T^2\|Y\|^2_{\mathcal H_l}$).
--   2. If $K\in\mathcal H_l$ with $l>0$, then $K_T=0$ a.s.
--   3. If $K_1\in\mathcal M_{-1}$ has a.s. continuous paths on $[0,T)$ and $K_2\in\mathcal H_l$, then $K_1K_2\in\mathcal H_{l-1}$.
--   4. $\mathcal M_l\subset\mathcal M_{l-1}$ and $\|Y\|_{\mathcal M_{l-1}}\le T\,\|Y\|_{\mathcal M_l}$.
--
--   In formulas, item 3 says that
--   $$\mathbb E\Big[\sup_{0\le t\le T}\frac{|K_1(t)K_2(t)|^2}{(T-t)^{2(l-1)}}\Big]<\infty .$$
--   These facts are the bookkeeping behind the method of continuation: $A\in\mathcal M_{-1}$ multiplies $X\in\mathcal H_\alpha$ into $\mathcal H_{\alpha-1}$, and membership in $\mathcal H_l$ encodes the liquidation constraint.
--
--   **Formalization Note** The paper's last line says "the first two properties also hold for the space $\mathcal M_l$". Only the first is stated (item 4): the $\mathcal M_l$ norm is an essential supremum over $dt\otimes d\mathbb P$, and $\{T\}\times\Omega$ is null, so "$K\in\mathcal M_l$, $l>0\Rightarrow K_T=0$" does not follow from the printed definition. Item 3 as printed ($K_1\in\mathcal M_{-1}$ only) is false for the same reason: the $\mathcal H$ norm takes a pointwise supremum over $t$, while $\mathcal M_{-1}$ controls $K_1$ only off a $dt\otimes d\mathbb P$-null set, on which $K_1$ may be arbitrarily large. The hypothesis that $K_1$ has a.s. continuous paths on $[0,T)$ (true of the Riccati solution $A$ in the paper) restores it. Norms are computed in $[0,\infty]$ with the weight $(T-t)^{-l}$ in `ℝ≥0∞`.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 8, Fact 2.2

import Mathlib
import Definitions.Def_MFGLiquidation_Equilibrium_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLiquidation.Equilibrium

open Peng1990.SMP

theorem fact_2_2 {Ω : Type*} [MeasurableSpace Ω] (G : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) [SFinite P] (T : ℝ≥0) (hT : 0 < T) :
    (∀ (l : ℝ) (Y : ℝ≥0 → Ω → ℝ), MemH G P T l Y →
      MemH G P T (l - 1) Y ∧ hNormSq T P (l - 1) Y ≤ (T : ℝ≥0∞) ^ 2 * hNormSq T P l Y) ∧
    (∀ (l : ℝ) (K : ℝ≥0 → Ω → ℝ), 0 < l → MemH G P T l K → ∀ᵐ ω ∂P, K T ω = 0) ∧
    (∀ (l : ℝ) (K₁ K₂ : ℝ≥0 → Ω → ℝ), MemM G P T (-1) K₁ →
      (∀ᵐ ω ∂P, ContinuousOn (fun t => K₁ t ω) (Set.Iio T)) → MemH G P T l K₂ →
      MemH G P T (l - 1) (fun t ω => K₁ t ω * K₂ t ω)) ∧
    (∀ (l : ℝ) (Y : ℝ≥0 → Ω → ℝ), MemM G P T l Y →
      MemM G P T (l - 1) Y ∧ mNorm T P (l - 1) Y ≤ (T : ℝ≥0∞) * mNorm T P l Y) := by sorry

end MFGLiquidation.Equilibrium
