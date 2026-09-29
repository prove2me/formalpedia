-- Prove2me | Theorems.Thm_HlawkaSchatten_norm_radialMazurHilbertMap
-- name    : HlawkaSchatten.norm_radialMazurHilbertMap
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:20:03.105279+00:00
-- url     : https://prove2.me/theorems/66f18fe7-3321-475d-94f3-c321c08731c3
-- title:
--   The radial Mazur map is an isometry of Schatten norms on individual operators
-- statement:
--   Let $E,F$ be finite-dimensional complex inner-product spaces, let $p>0$, and let $T:E\to F$ be a complex-linear map. Write
--
--   $$
--   \|T\|_p=\left(\sum_j\sigma_j(T)^p\right)^{1/p}
--   $$
--
--   for the Schatten $p$-quantity (`schattenPNorm`), where $\sigma_j(T)$ are the singular values. This is a norm for $p\ge1$ and a quasi-norm for $0<p<1$.
--
--   The *radial Mazur map* $\Psi_p$ is built as follows. At $T=0$, set $\Psi_p(0)=0$. Otherwise, normalize $T$ to the Schatten-$p$ power sphere by setting $U=\|T\|_p^{-1}T$, apply the rectangular Mazur map at exponent $p$ to $U$, and rescale its image by $\|T\|_p$. Record that operator by its column coordinates in a fixed orthonormal basis of $E$, giving a vector $\Psi_p(T)$ in a finite-dimensional Hilbert space. The theorem states that this construction preserves the size of each operator:
--
--   $$
--   \|\Psi_p(T)\|=\|T\|_p,
--   $$
--
--   where the norm on the left is the Hilbert-space norm.
--
--   This pointwise identity supplies the radii used in later comparisons of Schatten deficits with Hilbert-space deficits. It asserts no preservation of distances between two different operators. The map is generally nonlinear: sums of images and images of sums must be distinguished when forming those deficits.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/Final.lean#L75-L96

import Definitions.Def_HlawkaSchatten_Final
import Definitions.Def_HlawkaSchatten_SchattenNorm
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
# Dimension-independent Hlawka constants for Schatten norms

This file removes the unit-sphere normalization from the variational
comparison and performs the final Hilbert-space Hlawka transfer.
-/


open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

open HlawkaSchatten

theorem HlawkaSchatten.norm_radialMazurHilbertMap {p : ℝ} (hp : 0 < p)
    (T : E →ₗ[ℂ] F) :
    ‖radialMazurHilbertMap p T‖ = schattenPNorm p T := by sorry
