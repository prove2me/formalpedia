-- Prove2me | Theorems.Thm_HlawkaSchatten_dilatedBregmanTrace_self
-- name    : HlawkaSchatten.dilatedBregmanTrace_self
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:18:23.193965+00:00
-- url     : https://prove2.me/theorems/f8e84e70-db15-4ec0-b0b0-42dc6e89ca51
-- title:
--   The dilated trace-level Bregman divergence vanishes when compared against itself
-- statement:
--   Let $E,F$ be finite-dimensional complex inner-product spaces, let $p\in\mathbb R$ be arbitrary, and let $S:E\to F$ be a complex-linear map. The off-diagonal block operator $(x,y)\mapsto(S^*y,Sx)$ on $E\oplus F$ (with its Hilbert $\ell^2$ inner product), the *Hermitian dilation* of $S$, is self-adjoint for every complex-linear $S$; write $\widehat S$ for it.
--
--   For a self-adjoint operator $A$ on a finite-dimensional complex inner-product space, write $F_p(A)$ for the self-adjoint operator with the same eigenbasis as $A$ and eigenvalues $F_p(\lambda)=|\lambda|^p/p$ in place of each eigenvalue $\lambda$ of $A$ (and likewise $G_p(A)$, using $G_p(\lambda)=|\lambda|^{p-2}\lambda$). For two self-adjoint operators $A,B$ on the same space, define the trace-level Bregman quantity
--
--   $$
--   \beta_p^{\mathrm{tr}}(A,B) = \operatorname{Tr} F_p(A) - \operatorname{Tr} F_p(B) - \operatorname{Re}\operatorname{Tr}\bigl(A\circ G_p(B)\bigr) + \operatorname{Tr}\bigl(G_p(B)\circ B\bigr),
--   $$
--
--   where $G_p(B)\circ B$ is the operator with eigenvalues $G_p(\lambda)\lambda$ in $B$'s eigenbasis, not a scalar product. This is the direct operator lift of the scalar formula $\beta_p(a,b)=F_p(a)-F_p(b)-G_p(b)(a-b)$. For two complex-linear maps $S,T:E\to F$, the *dilated Bregman trace* is $B_p(S,T)=\beta_p^{\mathrm{tr}}(\widehat S,\widehat T)$. Then
--
--   $$
--   B_p(S,S) = 0.
--   $$
--
--   A Bregman-type divergence always vanishes when its two arguments coincide, since the first-order remainder of a function relative to itself is zero; this records that fact at the level of the dilated trace quantity, for the operator $S$ compared against itself. It is used to show that the normalized self-pairing of a unit-power-sphere operator equals one rather than zero, which is in turn what makes a weighted Bregman objective attain its minimum at the point built from the weighted operator sum.
--
--   **Formalization Note.** No hypothesis is placed on $p$: the identity is algebraic and holds for every real $p$, including values where $|x|^p/p$ is not convex or where the totalized real power and division behave in a way with no analytic meaning (e.g. $p=0$). The reading of $\beta_p^{\mathrm{tr}}$ as a genuine Bregman divergence — the first-order Taylor remainder of a convex function — is only meaningful when $p>1$, where $F_p$ is convex and differentiable with derivative $G_p$ (at $p=1$, $F_1=|x|$ is still convex, but $G_1$ is not its derivative at $0$); outside that range the same formula is still a well-defined real number, built from Lean's everywhere-defined real power and division, and this theorem's vanishing-on-the-diagonal fact holds for it regardless.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/HermitianDilation.lean#L613-L631

import Definitions.Def_HlawkaSchatten_HermitianDilation
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
# Rectangular Hermitian dilation

This file begins the passage from rectangular maps to the Hermitian spectral
comparison by constructing the standard off-diagonal dilation.
-/


open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

open HlawkaSchatten


@[simp]

theorem HlawkaSchatten.dilatedBregmanTrace_self (p : ℝ) (S : E →ₗ[ℂ] F) :
    dilatedBregmanTrace p S S = 0 := by sorry
