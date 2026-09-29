-- Prove2me | Theorems.Thm_HlawkaSchatten_exists_uniform_schattenPNorm_hlawkaConstant
-- name    : HlawkaSchatten.exists_uniform_schattenPNorm_hlawkaConstant
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:26:12.297693+00:00
-- url     : https://prove2.me/theorems/aec247d4-9cac-47ca-89dc-9fcf522a6bda
-- title:
--   A dimension-independent Hlawka constant for the Schatten $p$-norm, for every $p>1$
-- statement:
--   For every real exponent $p>1$, there exist real numbers $m,M$ with $0<m\le M$ such that, for *every* pair of finite-dimensional complex inner-product spaces $G,K$, the Schatten $p$-norm on complex-linear maps $G\to K$ satisfies Hlawka's inequality with constant $M/m$: writing $\|\cdot\|_p$ for the Schatten $p$-norm,
--   $$
--   \begin{aligned}
--   &\forall\, x,y,z : G\to K,\\
--   &\|x\|_p+\|y\|_p+\|z\|_p-\|x+y+z\|_p\\
--   &\quad\le\frac{M}{m}\Big[\big(\|x\|_p+\|y\|_p-\|x+y\|_p\big)\\
--   &\qquad\qquad+\big(\|x\|_p+\|z\|_p-\|x+z\|_p\big)\\
--   &\qquad\qquad+\big(\|y\|_p+\|z\|_p-\|y+z\|_p\big)\Big].
--   \end{aligned}
--   $$
--   Crucially, $m$ and $M$ depend only on $p$, not on the spaces $G,K$ or their dimensions.
--
--   This is the existence half of the project's main classification result: it packages a scalar compactness bound, a spectral lift, a Hermitian dilation, a radial Mazur map, and the classical Hilbert-space Hlawka inequality into a single dimension-independent Hlawka constant $M/m$ for the Schatten $p$-norm, for every interior exponent $p>1$. It is reused unchanged as the interior-existence conjunct of the top-level classification theorem, which additionally records the failure of any such constant at $p=1$ and $p=\infty$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/Final.lean#L238-L261

import Definitions.Def_HlawkaSchatten_GapComparison
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

theorem HlawkaSchatten.exists_uniform_schattenPNorm_hlawkaConstant
    {p : ℝ} (hp : 1 < p) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ {G K : Type*}
        [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K],
        HasHlawkaConstant
          (schattenPNorm p : (G →ₗ[ℂ] K) → ℝ) (M / m) := by sorry
