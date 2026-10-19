-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_planeIntegral_weight_slice
-- name    : OAI.TriangularHilbert.Heat.planeIntegral_weight_slice
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:05:20.137945+00:00
-- url     : https://prove2.me/theorems/fe3dbe5c-1cad-49db-9280-4bc7e33f5d8f
-- title:
--   Plane integrals of weighted slices split into finite sums
-- statement:
--   The Gaussian density is $\phi_\sigma(t)=(2\pi\sigma)^{-1/2}e^{-t^2/(2\sigma)}$, and the heat weight of a grid point $u$ with mesh $h$, centre $p$ and variance $\sigma$ is $h\,\phi_\sigma(u-p)$. Centres with $p_0+p_1+p_2=d$ are integrated by $\mathrm{planeIntegral}(f,d)=\int_{\mathbb R^2}f(z_1,z_2,d-z_1-z_2)\,dz$. Let $h>0$ and $\sigma_v>0$. For positions $a,b$, a finite family of positions $c_m$ with coefficients $f_m$, and a vertex $v$,
--   $$
--   \mathrm{planeIntegral}\Bigl(p\mapsto w_0(a)\,w_1(b)\sum_mf_m\,w_v(c_m)\Bigr)=\sum_mf_m\,\mathrm{planeIntegral}\bigl(p\mapsto w_0(a)\,w_1(b)\,w_v(c_m)\bigr),
--   $$
--   where $w_x(y)=h\phi_{\sigma_x}(y-p_x)$ is the heat weight at vertex $x$.
--
--   The plane integral is linear on these weighted slices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/WeightSlice.lean#L28-L43

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory
open scoped BigOperators
variable {ι : Type uι} [Fintype ι]

theorem OAI.TriangularHilbert.Heat.planeIntegral_weight_slice {h : ℝ} (hh : 0 < h) (a b d : ℝ)
    (c f : ι → ℝ) (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*
      ∑ m, f m*weight h (c m) (p v) (σ v)) d =
      ∑ m, f m*planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*weight h (c m) (p v) (σ v)) d := by sorry
