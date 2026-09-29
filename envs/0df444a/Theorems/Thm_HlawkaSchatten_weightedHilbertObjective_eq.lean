-- Prove2me | Theorems.Thm_HlawkaSchatten_weightedHilbertObjective_eq
-- name    : HlawkaSchatten.weightedHilbertObjective_eq
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:23:03.311058+00:00
-- url     : https://prove2.me/theorems/a483848e-a848-4178-9b89-e71267976671
-- title:
--   Closed form for the weighted Hilbert squared-distance objective
-- statement:
--   Let $\Bbbk$ be $\mathbb R$ or $\mathbb C$ (an instance of Mathlib's `RCLike`), let $H$ be an inner-product space over $\Bbbk$ (no finite-dimensionality is assumed), let $\iota$ be a finite index type, let $a:\iota\to\mathbb R$, and let $u:\iota\to H$ with $\|u_i\|=1$ for every $i$, and $v\in H$ with $\|v\|=1$. Write
--
--   $$
--   \mathrm{weightedHilbertObjective}(a,u,v) \;=\; \sum_{i\in\iota} a_i\,\|u_i-v\|^2
--   $$
--
--   for the weighted sum of squared distances from each $u_i$ to $v$, and $\mathrm{weightedHilbertSum}(a,u)=\sum_i a_i\,u_i$. Then
--
--   $$
--   \mathrm{weightedHilbertObjective}(a,u,v) \;=\; 2\Big(\sum_i a_i - \operatorname{Re}\big\langle \mathrm{weightedHilbertSum}(a,u),\,v\big\rangle_{\Bbbk}\Big),
--   $$
--
--   where $\langle\cdot,\cdot\rangle_{\Bbbk}$ is the inner product of $H$.
--
--   This closed form expresses the objective purely through the weighted sum $\sum_i a_iu_i$ and its inner product with $v$. This is exactly the algebraic shape needed to compute the objective's minimum over $v$ ranging on the unit sphere of $H$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/Variational.lean#L76-L94

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

theorem HlawkaSchatten.weightedHilbertObjective_eq
    (a : ι → ℝ) (u : ι → H) (v : H)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ‖v‖ = 1) :
    weightedHilbertObjective a u v =
      2 * (∑ i, a i -
        RCLike.re ⟪weightedHilbertSum (𝕜 := 𝕜) a u, v⟫_𝕜) := by sorry
