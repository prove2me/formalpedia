-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_int_intervals_weak
-- name    : OAI.TriangularHilbert.int_intervals_weak
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:12:31.85895+00:00
-- url     : https://prove2.me/theorems/d4b4969e-0316-4be0-ae00-f7747141b51a
-- title:
--   Weak-type Vitali bound for integer intervals
-- statement:
--   Let $D,s\subset\mathbb Z$ be finite and $f\ge0$ on $D$. Suppose each $n\in s$ has a radius $r(n)$ with large average:
--   $$
--   \rho\,(2r(n)+1)\le\sum_{m\in D,\ |m-n|\le r(n)}f(m)\qquad(n\in s),
--   $$
--   for some $\rho\ge0$. Then
--   $$
--   \rho\,|s|\le3\sum_{m\in D}f(m).
--   $$
--
--   This is the weak $(1,1)$ inequality for the discrete Hardy–Littlewood maximal function, with constant $3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/IntWeak.lean#L32-L70

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

open OAI OAI.TriangularHilbert
open scoped BigOperators

theorem OAI.TriangularHilbert.int_intervals_weak (D s : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (r : ℤ → ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hav : ∀ n ∈ s, ρ * (2*(r n:ℝ)+1) ≤ ∑ m ∈ D ∩ intInterval n (r n), f m) :
    ρ * (s.card:ℝ) ≤ 3 * ∑ m ∈ D, f m := by sorry
