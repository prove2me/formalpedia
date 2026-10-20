-- Prove2me | Theorems.Thm_OAI_finiteLaplaceSum_vertical_bound_of_sector_resolvent
-- name    : OAI.finiteLaplaceSum_vertical_bound_of_sector_resolvent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:06:32.108146+00:00
-- url     : https://prove2.me/theorems/40abb04f-5681-432e-87c7-4178fbc1dbc9
-- title:
--   Bounding finite Laplace sums by sectorial resolvent estimates
-- statement:
--   Let $a>0$ and $M\ge0$. There are $\sigma>0$ and $B\ge0$ with the following property. Let $E$ be a complex Banach space, $\lambda_1,\dots,\lambda_k\ge0$ and $v_1,\dots,v_k\in E$. Suppose that for every nonzero $z$ with $\mathrm{Re}\,z\le a|\mathrm{Im}\,z|$,
--   $$
--   \Bigl\|\sum_i\frac{v_i}{z-\lambda_i}\Bigr\|\le\frac M{|z|}.
--   $$
--   Then $\bigl\|\sum_ie^{-(\sigma+i\tau)\lambda_i}v_i\bigr\|\le B$ for every $\tau\in[-\pi,\pi]$.
--
--   The bound is independent of $E$, $k$, the $\lambda_i$ and the $v_i$; only the sectorial resolvent constant matters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/FiniteContour.lean#L363-L473

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour

open OAI
open Complex Set MeasureTheory Filter
open scoped BigOperators Interval Topology

open FiniteContour in
theorem OAI.finiteLaplaceSum_vertical_bound_of_sector_resolvent
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    ∃ T B : ℝ, 0 < T ∧ 0 ≤ B ∧
      ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
        [CompleteSpace E] (ι : Type*) [Fintype ι]
        (lam : ι → ℝ) (v : ι → E),
        (∀ i, 0 ≤ lam i) →
        (∀ z : ℂ, z ≠ 0 → z.re ≤ a * |z.im| →
          ‖∑ i, (z - (lam i : ℂ))⁻¹ • v i‖ ≤ M / ‖z‖) →
        ∀ tau : ℝ, |tau| ≤ Real.pi →
          ‖∑ i, Complex.exp (-(((T : ℂ) + (tau : ℂ) * Complex.I) *
            (lam i : ℂ))) • v i‖ ≤ B := by sorry
