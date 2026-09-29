-- Prove2me | Theorems.Thm_HlawkaSchatten_weightedHilbertObjective_isGlobalMinimumValue
-- name    : HlawkaSchatten.weightedHilbertObjective_isGlobalMinimumValue
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:23:19.780762+00:00
-- url     : https://prove2.me/theorems/25b50463-5ab1-4ef5-a9e7-10131b88e295
-- title:
--   The weighted Hilbert objective attains its minimum on the unit sphere
-- statement:
--   Let $\Bbbk$ be $\mathbb R$ or $\mathbb C$, let $H$ be an inner-product space over $\Bbbk$ (no finite-dimensionality is assumed), let $\iota$ be a nonempty finite index type, let $a:\iota\to\mathbb R$ and $u:\iota\to H$ with $\|u_i\|=1$ for every $i$. Write $\mathrm{weightedHilbertSum}(a,u)=\sum_ia_iu_i$ and, for $v$ on the unit sphere of $H$ (the set of vectors of norm $1$),
--
--   $$
--   \mathrm{weightedHilbertObjective}(a,u,v) = \sum_i a_i\,\|u_i-v\|^2.
--   $$
--
--   Then this objective, as a function of $v$ ranging over the unit sphere of $H$, attains the global minimum value
--
--   $$
--   2\Big(\sum_i a_i - \big\|\mathrm{weightedHilbertSum}(a,u)\big\|\Big).
--   $$
--
--   This computes the exact minimum of the weighted sum-of-squared-distances objective over all unit vectors, in closed form through the norm of the weighted sum $\sum_ia_iu_i$ alone. It is the Hilbert-space side of the variational comparison used to bound triple and pair deficits after the rectangular Mazur map.
--
--   **Formalization Note** No sign condition is placed on the weights $a_i$. When $\mathrm{weightedHilbertSum}(a,u)=0$ the objective is the constant $2\sum_ia_i$ on the whole unit sphere, so any $u_i$ is a minimizer; this is where $\iota$ nonempty is used, since the sphere must contain a point.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/Variational.lean#L96-L142

import Definitions.Def_HlawkaSchatten_Basic
import Definitions.Def_HlawkaSchatten_Variational
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Variational minima for the Bregman--Mazur argument

This file proves two reusable parts of the variational layer.  First, a
pointwise two-sided comparison transports to attained global minima, even
when the two objectives are indexed by different but equivalent spheres.
Second, the weighted squared-distance objective on a Hilbert unit sphere has
the exact minimum used in the Schatten argument.
-/


open scoped InnerProductSpace ComplexConjugate







variable {𝕜 H ι : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

open HlawkaSchatten

theorem HlawkaSchatten.weightedHilbertObjective_isGlobalMinimumValue
    [Nonempty ι] (a : ι → ℝ) (u : ι → H)
    (hu : ∀ i, ‖u i‖ = 1) :
    IsGlobalMinimumValue
      (fun v : unitSphere H ↦ weightedHilbertObjective a u v.1)
      (2 * (∑ i, a i - ‖weightedHilbertSum (𝕜 := 𝕜) a u‖)) := by sorry
