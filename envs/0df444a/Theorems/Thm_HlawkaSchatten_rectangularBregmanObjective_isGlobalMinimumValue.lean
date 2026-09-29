-- Prove2me | Theorems.Thm_HlawkaSchatten_rectangularBregmanObjective_isGlobalMinimumValue
-- name    : HlawkaSchatten.rectangularBregmanObjective_isGlobalMinimumValue
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:22:24.5024+00:00
-- url     : https://prove2.me/theorems/f6170b30-7be3-48f5-a6f5-f032f3d8b52b
-- title:
--   The rectangular Bregman objective attains its minimum on the Schatten power sphere
-- statement:
--   Let $E,F$ be finite-dimensional complex inner-product spaces, let $\iota$ be a nonempty finite index type, let $p\in\mathbb R$ with $p>1$, and let $a:\iota\to\mathbb R$ (no sign condition on $a$). For a complex-linear map $T:E\to F$ with singular values $\operatorname{sv}_k(T)$, the *Schatten $p$-power sphere* is $\{T\mid\sum_k\operatorname{sv}_k(T)^p=1\}$ (`schattenPowerSphere`), and let $u:\iota\to$ (that sphere).
--
--   For $T:E\to F$, write $\widehat T$ for its *Hermitian dilation*, the self-adjoint operator on $E\oplus F$ with $\widehat T(x,y)=(T^\ast y,\,Tx)$ (`hermitianDilation`). For a self-adjoint operator $C$ and $h:\mathbb R\to\mathbb R$, write $h(C)$ for the result of applying $h$ to $C$'s eigenvalues in any orthonormal eigenbasis of $C$; this operator itself does not depend on which eigenbasis is chosen, since it acts as $h(\mu)$ on every $\mu$-eigenvector of $C$, not only on the vectors of one particular chosen eigenbasis — which is what lets $\widehat S\circ G_p(\widehat T)$ and $\widehat T\circ G_p(\widehat T)$ below be single well-defined operators. For $S,T:E\to F$, the *dilated Bregman trace* is
--
--   $$
--   B_p(S,T) \;=\; \operatorname{Tr}F_p(\widehat S) - \operatorname{Tr}F_p(\widehat T) - \operatorname{Re}\operatorname{Tr}\!\big(\widehat S\circ G_p(\widehat T)\big) + \operatorname{Tr}\!\big(\widehat T\circ G_p(\widehat T)\big)
--   $$
--
--   (`dilatedBregmanTrace`), with $F_p(x)=|x|^p/p$ and $G_p(x)=|x|^{p-2}x$. The *rectangular Bregman objective* is the half-dilated weighted sum
--
--   $$
--   \mathrm{rectangularBregmanObjective}(p,a,u,v) \;=\; \sum_{i\in\iota} a_i\cdot\frac{B_p(u_i,v)}{2},
--   $$
--
--   as a function of $v$ ranging over the Schatten $p$-power sphere, and $\mathrm{rectangularWeightedSum}(a,u)=\sum_i a_i\,u_i$ is the (unnormalized) weighted sum of the underlying maps. Writing $\|T\|_p=\big(\sum_k\operatorname{sv}_k(T)^p\big)^{1/p}$ for the Schatten $p$-norm (`schattenPNorm`), the theorem states that $\mathrm{rectangularBregmanObjective}(p,a,u,\cdot)$ attains the global minimum value
--
--   $$
--   \Big(\sum_{i\in\iota} a_i\Big) - \big\|\mathrm{rectangularWeightedSum}(a,u)\big\|_p
--   $$
--
--   over the Schatten $p$-power sphere.
--
--   This is the operator-level analogue, for the Schatten $p$-norm on rectangular maps, of the exact Hilbert-space minimum of a weighted squared-distance objective: it is one of the two variational facts (the other being the analogous minimum for the paired Mazur-distance objective) whose comparison produces the two-sided bound between triple and pair deficits that this construction needs.
--
--   **Formalization Note** The Schatten $p$-power sphere is defined by $\sum_k\operatorname{sv}_k(T)^p=1$; for $p>0$ this is equivalent to $\|T\|_p=1$ (`schattenPNorm_eq_one_iff`). In this theorem's range $p>1$, $F_p$ is convex and differentiable with derivative $G_p$. The proof uses the resulting scalar Bregman nonnegativity through a supporting theorem, then lifts it to $B_p$ by the spectral trace identity.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/Variational.lean#L233-L310

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

theorem HlawkaSchatten.rectangularBregmanObjective_isGlobalMinimumValue
    [Nonempty ι] {p : ℝ} (hp : 1 < p) (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    IsGlobalMinimumValue (rectangularBregmanObjective p a u)
      ((∑ i, a i) - schattenPNorm p (rectangularWeightedSum a u)) := by sorry
