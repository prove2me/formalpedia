-- Prove2me | Theorems.Thm_HlawkaSchatten_finiteFamilyGap_two_sided
-- name    : HlawkaSchatten.finiteFamilyGap_two_sided
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:23:57.256824+00:00
-- url     : https://prove2.me/theorems/e19a3ce9-4c16-438d-a37d-22fcb5cdab8b
-- title:
--   Two-sided comparison of a Schatten family deficit with its radial Mazur image
-- statement:
--   Let $E,F$ be finite-dimensional complex inner-product spaces, let $\iota$ be a nonempty finite index set, let $p>1$, and let $m,M\in\mathbb{R}$ with $m\ge0$. Let $(x_i)_{i\in\iota}$ be a family of **nonzero** complex-linear maps $E\to F$. Write $\|\cdot\|_p$ for the Schatten $p$-norm and $\|\cdot\|_2$ for the Schatten-$2$ (Hilbert–Schmidt) norm (`schattenPNorm`). Let $M_p(T)$ be the rectangular Mazur map (`rectangularMazurMap`): apply the odd scalar map $t\mapsto\operatorname{sign}(t)|t|^{p/2}$ to the eigenvalues of the Hermitian dilation $\widehat T(\xi,\eta)=(T^\ast\eta,T\xi)$ on $E\oplus F$, then take the lower-left block. Define its radial version $\Phi_p$ (`radialRectangularMazurMap`) by
--
--   $$
--   \Phi_p(T)=\|T\|_p\,M_p\!\left(\frac{T}{\|T\|_p}\right)\quad(T\ne0),\qquad \Phi_p(0)=0.
--   $$
--
--   Thus $\|\Phi_p(T)\|_2=\|T\|_p$ for every $T$.
--
--   For any two complex-linear maps $S,T:E\to F$, write $B_p(S,T)$ (`dilatedBregmanTrace`) and $D_p(S,T)$ (`dilatedMazurDistanceSq`) for the trace-level Bregman divergence and squared Mazur distance, at exponent $p$, between the two Hermitian dilations $\widehat S$ and $\widehat T$ on $E\oplus F$ — built respectively from the scalar potential $|t|^p/p$ and the odd power map $t\mapsto\operatorname{sign}(t)|t|^{p/2}$. Suppose there is a uniform two-sided bound
--   $$
--   m\,D_p(S,T) \;\le\; B_p(S,T) \;\le\; M\,D_p(S,T)
--   $$
--   holding for *every* pair of maps $S,T:E\to F$. Then
--   $$
--   2m\Big(\sum_{i} \|x_i\|_p - \big\|\textstyle\sum_i \Phi_p(x_i)\big\|_2\Big) \;\le\; \sum_i \|x_i\|_p - \Big\|\sum_i x_i\Big\|_p \;\le\; 2M\Big(\sum_i \|x_i\|_p - \big\|\textstyle\sum_i \Phi_p(x_i)\big\|_2\Big).
--   $$
--
--   This bounds, on both sides, the actual multi-operator Schatten-$p$ deficit $\sum_i\|x_i\|_p-\|\sum_i x_i\|_p$ of a whole finite family by the corresponding deficit computed after mapping every operator, radially, into Hilbert–Schmidt space. Specializing $\iota$ to two or three elements produces the pair and triple deficit comparisons used later in the assembly of the dimension-independent Hlawka constant.
--
--   **Formalization Note** The quantity $\|\sum_i\Phi_p(x_i)\|_2$ on the two outer sides is the Schatten-$2$ norm of a sum of operators. Evaluating an operator on a fixed orthonormal basis of $E$ is linear, and the Schatten-$2$ norm of an operator is the Hilbert-space norm of that family of values (`schattenPNorm_two_eq_norm_hilbertSchmidtCoordinates`), so this quantity also equals $\|\sum_i\Psi_p(x_i)\|$, where $\Psi_p(x_i)$ (`radialMazurHilbertMap p (x_i)`) is $\Phi_p(x_i)$ recorded by its values on that basis.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/Final.lean#L105-L136

import Definitions.Def_HlawkaSchatten_Final
import Definitions.Def_HlawkaSchatten_HermitianDilation
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

theorem HlawkaSchatten.finiteFamilyGap_two_sided
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p m M : ℝ} (hp : 1 < p) (hm : 0 ≤ m)
    (x : ι → E →ₗ[ℂ] F) (hx : ∀ i, x i ≠ 0)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    2 * m * ((∑ i, schattenPNorm p (x i)) - schattenPNorm 2
        (∑ i, radialRectangularMazurMap p (x i))) ≤
        (∑ i, schattenPNorm p (x i)) - schattenPNorm p (∑ i, x i) ∧
      (∑ i, schattenPNorm p (x i)) - schattenPNorm p (∑ i, x i) ≤
        2 * M * ((∑ i, schattenPNorm p (x i)) - schattenPNorm 2
          (∑ i, radialRectangularMazurMap p (x i))) := by sorry
