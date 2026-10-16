-- Prove2me | Theorems.Thm_OAI_ThreeManifold_ReturningCoefficients_psd_cauchy
-- name    : OAI.ThreeManifold.ReturningCoefficients.psd_cauchy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:30:41.900702+00:00
-- url     : https://prove2.me/theorems/a3aba4df-955f-4dad-b9cb-eb35f5fdb7d6
-- title:
--   Cauchy–Schwarz inequality for a positive semidefinite symmetric $2\times 2$ matrix
-- statement:
--   Let $D$ be a real $2 \times 2$ matrix that is symmetric, $D^{\top} = D$, and positive semidefinite in the sense that $q^{\top} D q \ge 0$ for every $q \in \mathbb{R}^2$. Then for all $p, q \in \mathbb{R}^2$,
--   $$
--   \big(p^{\top} D q\big)^2 \le \big(p^{\top} D p\big)\big(q^{\top} D q\big).
--   $$
--
--   This is the Cauchy–Schwarz inequality for the (possibly degenerate) symmetric bilinear form $(p,q) \mapsto p^{\top} D q$. It is used to bound mixed terms $p^{\top} D e$ of difference matrices $D$ by their diagonal values in the estimates for returning geodesic passages.
--
--   **Formalization Note** The bilinear form is `pairing D p q`, defined as the dot product of $p$ with $D q$, on vectors of type `TVec` $= \mathbb{R}^2$ and matrices of type `TMat`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Returning.lean#L688-L701

import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning

open OAI OAI.ThreeManifold OAI.ThreeManifold.ReturningCoefficients
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval
open Neck Matrix

theorem OAI.ThreeManifold.ReturningCoefficients.psd_cauchy {D : TMat} (hD : Dᵀ = D)
    (hpos : ∀ q, 0 ≤ pairing D q q) (p q : TVec) :
    pairing D p q ^ 2 ≤ pairing D p p * pairing D q q := by sorry
