-- Prove2me | Theorems.Thm_HlawkaSchatten_rectangularMazurDistanceObjective_isGlobalMinimumValue
-- name    : HlawkaSchatten.rectangularMazurDistanceObjective_isGlobalMinimumValue
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:23:37.850612+00:00
-- url     : https://prove2.me/theorems/c080cfc6-be38-4685-832d-c6a707d552d9
-- title:
--   The rectangular Mazur-distance objective attains its minimum on the Schatten power sphere
-- statement:
--   Let $E,F$ be finite-dimensional complex inner-product spaces, let $\kappa$ be a finite index type and $e$ an orthonormal basis of $E$ indexed by $\kappa$, let $p\in\mathbb R$ with $p>0$, and let $\iota$ be a nonempty finite index type. For a complex-linear map $T:E\to F$ with singular values $\operatorname{sv}_k(T)$, the *Schatten $p$-power sphere* is $\{T\mid\sum_k\operatorname{sv}_k(T)^p=1\}$ (`schattenPowerSphere`). For $T:E\to F$ write $\widehat T$ for its Hermitian dilation, the self-adjoint operator on $E\oplus F$ with $\widehat T(x,y)=(T^\ast y,\,Tx)$ (`hermitianDilation`), and let $\psi_p(x)=\operatorname{sign}(x)\,|x|^{p/2}$ be the scalar Mazur map (`scalarMazur`). Applying $\psi_p$ to the eigenvalues of $\widehat T$ in an orthonormal eigenbasis gives a self-adjoint operator that is again the dilation of a unique complex-linear map $E\to F$; that map is the *rectangular Mazur map* $\Psi_p(T)$ (`rectangularMazurMap`), so $\widehat{\Psi_p(T)}=\psi_p(\widehat T)$. It satisfies $\sum_k\operatorname{sv}_k(\Psi_p(T))^2=\sum_k\operatorname{sv}_k(T)^p$, so it sends the Schatten $p$-power sphere into the ordinary Schatten-$2$ (Hilbert–Schmidt) unit sphere.
--
--   Fix real weights $a:\iota\to\mathbb R$ (no sign condition on the $a_i$) and a family $(u_i)_{i\in\iota}$ on the Schatten $p$-power sphere. For $v$ ranging over the same sphere, consider the weighted objective
--
--   $$
--   f(v) \;=\; \sum_{i\in\iota} a_i\,\big\|\Psi_p(u_i)-\Psi_p(v)\big\|_2^2 \qquad (\texttt{rectangularMazurDistanceObjective}),
--   $$
--
--   with $\|\cdot\|_2$ the Schatten-$2$ norm, and let $w=\sum_{i\in\iota}a_i\,\Psi_p(u_i)$ be the weighted barycenter of the Mazur images (`rectangularMazurBarycenter`). Then the theorem states that $f$ attains the global minimum value
--
--   $$
--   2\Big(\sum_{i\in\iota}a_i - \|w\|_2\Big)
--   $$
--
--   over the Schatten $p$-power sphere: this value lower-bounds $f(v)$ for every $v$ on the sphere, and equals $f(v)$ for some $v$ on the sphere.
--
--   This is the Hilbert-side half of the variational comparison: it computes, in closed form, the minimum of the weighted squared-distance objective on the actual Schatten power sphere of rectangular operators — with no enlargement to an ambient coordinate space — matching the identity $\min_{\|v\|=1}\sum_ia_i\|u_i-v\|^2=2\big(\sum_ia_i-\|\sum_ia_iu_i\|\big)$ for unit vectors $u_i$ in an ordinary Hilbert space.
--
--   **Formalization Note** The statement is additionally parametrized by an orthonormal basis $e$ of $E$ indexed by $\kappa$, used only to identify Hilbert–Schmidt coordinates on $E$ in the proof; neither the objective, the barycenter, nor the minimum value depends on the choice of $e$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/Variational.lean#L419-L457

import Definitions.Def_HlawkaSchatten_SchattenNorm
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











section RectangularMazur

variable {E F κ : Type*} [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

open HlawkaSchatten

theorem HlawkaSchatten.rectangularMazurDistanceObjective_isGlobalMinimumValue
    (e : OrthonormalBasis κ ℂ E) [Nonempty ι]
    {p : ℝ} (hp : 0 < p) (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    IsGlobalMinimumValue (rectangularMazurDistanceObjective p a u)
      (2 * (∑ i, a i - schattenPNorm 2
        (rectangularMazurBarycenter p a u))) := by sorry
