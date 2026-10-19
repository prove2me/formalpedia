-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_int_intervals_strong
-- name    : OAI.TriangularHilbert.int_intervals_strong
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:13:14.87199+00:00
-- url     : https://prove2.me/theorems/9dabe308-c28e-42cd-955b-4658586421e7
-- title:
--   Strong three-halves bound for integer interval averages
-- statement:
--   Let $D,s\subset\mathbb Z$ be finite, $f\ge0$ on $D$ and $g\ge0$ on $s$. Suppose each $n\in s$ has a radius $r(n)$ with
--   $$
--   g(n)\,(2r(n)+1)\le\sum_{m\in D,\ |m-n|\le r(n)}f(m).
--   $$
--   Then
--   $$
--   \sum_{n\in s}g(n)^{3/2}\le18\sqrt2\sum_{m\in D}f(m)^{3/2}.
--   $$
--
--   This is the $\ell^{3/2}$ bound for the discrete Hardy–Littlewood maximal function, by interpolation from the weak $(1,1)$ bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/IntStrong.lean#L28-L79

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer

open OAI OAI.TriangularHilbert
open MeasureTheory
open scoped BigOperators

theorem OAI.TriangularHilbert.int_intervals_strong (D s : Finset ℤ) (f g : ℤ → ℝ)
    (hf : ∀ m ∈ D, 0 ≤ f m) (hg : ∀ n ∈ s, 0 ≤ g n) (r : ℤ → ℕ)
    (hav : ∀ n ∈ s, g n*(2*(r n:ℝ)+1) ≤ ∑ m ∈ D ∩ intInterval n (r n), f m) :
    (∑ n ∈ s, g n*Real.sqrt (g n)) ≤
      18*Real.sqrt 2 * ∑ m ∈ D, f m*Real.sqrt (f m) := by sorry
