-- Prove2me | Theorems.Thm_HlawkaSchatten_pairGap_radial_two_sided
-- name    : HlawkaSchatten.pairGap_radial_two_sided
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:24:22.124954+00:00
-- url     : https://prove2.me/theorems/7cb6c299-e5e1-4f0f-b194-365cff4500dc
-- title:
--   Two-sided pair-deficit comparison for the Schatten $p$-norm via the radial Mazur map
-- statement:
--   Let $E,F$ be finite-dimensional complex inner-product spaces, let $p>1$, let $m,M\in\mathbb{R}$ with $m\ge0$, and let $x,y:E\to F$ be any two complex-linear maps, possibly zero. Write $\|\cdot\|_p$ for the Schatten $p$-norm (`schattenPNorm`). The rectangular Mazur map $M_p$ (`rectangularMazurMap`) is obtained by applying $t\mapsto\operatorname{sign}(t)|t|^{p/2}$ to the eigenvalues of the Hermitian dilation $\widehat T(\xi,\eta)=(T^\ast\eta,T\xi)$ on $E\oplus F$, then taking the lower-left block. It carries the Schatten-$p$ power sphere onto the Schatten-$2$ power sphere. It is generally nonlinear; at $p=2$ it is the identity. Define the radial rectangular image $\Phi_p$ (`radialRectangularMazurMap`) by
--
--   $$
--   \Phi_p(T)=\|T\|_p\,M_p\!\left(\frac{T}{\|T\|_p}\right)\quad(T\ne0),\qquad \Phi_p(0)=0.
--   $$
--
--   Record $\Phi_p(T)$ by its values on a fixed orthonormal basis of $E$, obtaining the vector $\Psi_p(T)$ in the Hilbert space of column tuples with its $\ell^2$ norm (`radialMazurHilbertMap`). Then $\Psi_p(0)=0$ and $\|\Psi_p(T)\|=\|T\|_p$ for every $T$. Define the pair deficit and its mapped counterpart by
--
--   $$
--   \mathrm{pgap}(x,y)=\|x\|_p+\|y\|_p-\|x+y\|_p,\qquad
--   \mathrm{mpgap}(x,y)=\|x\|_p+\|y\|_p-\|\Psi_p(x)+\Psi_p(y)\|.
--   $$
--
--   For any two complex-linear maps $S,T:E\to F$, write $B_p(S,T)$ (`dilatedBregmanTrace`) and $D_p(S,T)$ (`dilatedMazurDistanceSq`) for the trace-level Bregman divergence and squared Mazur distance, at exponent $p$, between the two Hermitian dilations $\widehat S$ and $\widehat T$ on $E\oplus F$, built respectively from the scalar potential $|t|^p/p$ and the odd map $t\mapsto\operatorname{sign}(t)|t|^{p/2}$. Assume the uniform two-sided bound
--   $$
--   m\,D_p(S,T)\le B_p(S,T)\le M\,D_p(S,T)
--   $$
--   holds for every pair $S,T:E\to F$. Then
--   $$
--   2m\cdot\mathrm{mpgap}(x,y) \;\le\; \mathrm{pgap}(x,y) \;\le\; 2M\cdot\mathrm{mpgap}(x,y).
--   $$
--
--   This is the two-operator (pair) specialization of the family-level deficit estimate, extended to cover the edge cases where $x$, $y$, or both vanish. When $m>0$, its lower bound combines with the triple-operator upper bound and Hilbert-space Hlawka inequality in the final argument. If the same constants work in every dimension, this yields a dimension-independent Hlawka constant $M/m$ for the Schatten $p$-norm.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/Final.lean#L177-L209

import Definitions.Def_HlawkaSchatten_Final
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_HermitianDilation
import Definitions.Def_HlawkaSchatten_MazurGapComparison
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

theorem HlawkaSchatten.pairGap_radial_two_sided
    {p m M : ℝ} (hp : 1 < p) (hm : 0 ≤ m)
    (x y : E →ₗ[ℂ] F)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    2 * m * mappedPairGap (schattenPNorm p) (radialMazurHilbertMap p) x y ≤
        pairGap (schattenPNorm p) x y ∧
      pairGap (schattenPNorm p) x y ≤
        2 * M * mappedPairGap (schattenPNorm p) (radialMazurHilbertMap p) x y := by sorry
