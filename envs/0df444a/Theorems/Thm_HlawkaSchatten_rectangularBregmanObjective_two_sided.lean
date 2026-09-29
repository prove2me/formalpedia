-- Prove2me | Theorems.Thm_HlawkaSchatten_rectangularBregmanObjective_two_sided
-- name    : HlawkaSchatten.rectangularBregmanObjective_two_sided
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:22:43.517989+00:00
-- url     : https://prove2.me/theorems/7e0225e2-5322-484b-a9d2-0d65e7844ae1
-- title:
--   Weighted two-sided comparison between the rectangular Bregman and Mazur-distance objectives
-- statement:
--   Let $E,F$ be finite-dimensional complex inner-product spaces and let $p$ be any real number (no hypothesis is placed on $p$ in this statement). For a complex-linear map $T:E\to F$, write $\widehat T$ for its *Hermitian dilation*, the self-adjoint operator on $E\oplus F$ given by $\widehat T(x,y)=(T^\ast y,\,Tx)$ (`hermitianDilation`). For a self-adjoint operator $C$ on $E\oplus F$ and $h:\mathbb R\to\mathbb R$, write $h(C)$ for the operator obtained by applying $h$ to the eigenvalues of $C$ in any orthonormal eigenbasis of $C$; this operator itself does not depend on which eigenbasis is chosen, since it acts as $h(\mu)$ on every $\mu$-eigenvector of $C$, not only on the vectors of one particular chosen eigenbasis — which is what lets $\psi_p(\widehat S)\circ\psi_p(\widehat T)$ below be a single well-defined operator even though $\widehat S$ and $\widehat T$ generally have different eigenbases. With $F_p(x)=|x|^p/p$, $G_p(x)=|x|^{p-2}x$, and the scalar Mazur map $\psi_p(x)=\operatorname{sign}(x)\,|x|^{p/2}$ (`powerPotential`, `powerGradient`, `scalarMazur`; all three are totalized real powers, defined for every real $p$ and $x$), set
--
--   $$
--   B_p(S,T) \;=\; \operatorname{Tr}F_p(\widehat S) - \operatorname{Tr}F_p(\widehat T) - \operatorname{Re}\operatorname{Tr}\!\big(\widehat S\circ G_p(\widehat T)\big) + \operatorname{Tr}\!\big(\widehat T\circ G_p(\widehat T)\big)
--   $$
--
--   (`dilatedBregmanTrace`, the trace-level Bregman combination of $F_p$ between $\widehat S$ and $\widehat T$) and
--
--   $$
--   D_p(S,T) \;=\; \operatorname{Tr}\big(\psi_p(\widehat S)^2\big) - 2\operatorname{Re}\operatorname{Tr}\big(\psi_p(\widehat S)\circ\psi_p(\widehat T)\big) + \operatorname{Tr}\big(\psi_p(\widehat T)^2\big)
--   $$
--
--   (`dilatedMazurDistanceSq`, the squared Hilbert–Schmidt distance $\operatorname{Tr}\big((\psi_p(\widehat S)-\psi_p(\widehat T))^2\big)$ between the Mazur images of the two dilations). Separately, let $\Psi_p(T):E\to F$ be the *rectangular Mazur map* of $T$ — the unique complex-linear map whose dilation is $\psi_p(\widehat T)$, i.e. $\widehat{\Psi_p(T)}=\psi_p(\widehat T)$ (`rectangularMazurMap`); it satisfies $D_p(S,T) = 2\,\|\Psi_p(S)-\Psi_p(T)\|_2^2$, where $\|\cdot\|_2$ is the Schatten-$2$ (Hilbert–Schmidt) norm.
--
--   For $T:E\to F$ with singular values $\operatorname{sv}_k(T)$, the *Schatten $p$-power sphere* is $\{T\mid\sum_{k:\,\operatorname{sv}_k(T)\ne0}\operatorname{sv}_k(T)^p=1\}$ (`schattenPowerSphere`; the sum runs over the nonzero singular values, which for $p>0$ is the same as summing over all of them). Let $\iota$ be a finite index type, let $a:\iota\to\mathbb R$ with $a_i\ge0$ for every $i$, let $(u_i)_{i\in\iota}$ be a family on the Schatten $p$-power sphere, and let $v$ be a further point on that sphere. Define the *rectangular Bregman objective* and *rectangular Mazur-distance objective*
--
--   $$
--   \begin{aligned}
--   &\mathrm{rectangularBregmanObjective}(p,a,u,v)\\
--   &\quad= \sum_i a_i\cdot\frac{B_p(u_i,v)}{2},\\
--   &\mathrm{rectangularMazurDistanceObjective}(p,a,u,v)\\
--   &\quad= \sum_i a_i\,\big\|\Psi_p(u_i)-\Psi_p(v)\big\|_2^2
--   \end{aligned}
--   $$
--
--   (the second equals $\sum_i a_i\,D_p(u_i,v)/2$ as well, since $D_p(S,T)=2\|\Psi_p(S)-\Psi_p(T)\|_2^2$). Assume real numbers $m,M$ satisfy the pointwise two-sided bound
--
--   $$
--   m\,D_p(S,T) \;\le\; B_p(S,T) \;\le\; M\,D_p(S,T)
--   $$
--
--   for every pair of complex-linear maps $S,T:E\to F$. Then the theorem states
--
--   $$
--   \begin{aligned}
--   &m\cdot\mathrm{rectangularMazurDistanceObjective}(p,a,u,v)\\
--   &\quad\le\mathrm{rectangularBregmanObjective}(p,a,u,v)\\
--   &\quad\le M\cdot\mathrm{rectangularMazurDistanceObjective}(p,a,u,v).
--   \end{aligned}
--   $$
--
--   This lifts a pairwise two-sided bound between $B_p$ and $D_p$, assumed uniformly over rectangular operators, to the weighted finite-family objectives that the variational argument minimizes over the Schatten power sphere, with the same constants $m,M$.
--
--   **Formalization Note** Both named objectives already carry the same $\tfrac12$ normalization relative to $B_p$ and $D_p$ respectively (one directly, the other through the identity $D_p(S,T)=2\|\Psi_p(S)-\Psi_p(T)\|_2^2$), so the displayed two-sided bound needs no extra factor on either side. No convexity of $F_p$ is claimed or needed here, since $p$ ranges over all of $\mathbb R$; $B_p$ and $D_p$ are used purely as totalized algebraic quantities, and the two-sided bound between them is assumed as a hypothesis on this page, not derived from convexity.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/Variational.lean#L312-L359

import Definitions.Def_HlawkaSchatten_HermitianDilation
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

theorem HlawkaSchatten.rectangularBregmanObjective_two_sided
    (p m M : ℝ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (v : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    m * rectangularMazurDistanceObjective p a u v ≤
        rectangularBregmanObjective p a u v ∧
      rectangularBregmanObjective p a u v ≤
        M * rectangularMazurDistanceObjective p a u v := by sorry
