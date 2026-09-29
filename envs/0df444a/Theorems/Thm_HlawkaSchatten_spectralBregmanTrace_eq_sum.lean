-- Prove2me | Theorems.Thm_HlawkaSchatten_spectralBregmanTrace_eq_sum
-- name    : HlawkaSchatten.spectralBregmanTrace_eq_sum
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:21:41.976006+00:00
-- url     : https://prove2.me/theorems/d0228a27-ac67-49d8-a52e-43b8e659a9b7
-- title:
--   The spectral Bregman trace as an overlap-weighted sum of scalar Bregman terms
-- statement:
--   Fix a finite-dimensional complex inner-product space $E$ and a real number $p$ (no hypothesis is placed on $p$). Let $(e_i)_{i\in\iota}$ and $(f_j)_{j\in\kappa}$ be orthonormal bases of $E$ indexed by finite index types $\iota,\kappa$, and let $a:\iota\to\mathbb R$, $b:\kappa\to\mathbb R$ be real numbers attached to them. For an orthonormal basis $e$ and real numbers $c$, write $\mathrm{diag}_e(c)$ for the self-adjoint operator on $E$ with $\mathrm{diag}_e(c)\,e_i = c_i\,e_i$ for every $i$ (`spectralDiagonal`), and for a function $h:\mathbb R\to\mathbb R$ write $h(c)$ for the tuple $i\mapsto h(c_i)$, so $\mathrm{diag}_e(h(c))$ is the operator with eigenvalues $h(c_i)$; we also write $h(\mathrm{diag}_e(c))$ for this same operator.
--
--   With $F_p(x) = |x|^p/p$ and $G_p(x) = |x|^{p-2}x$, the *spectral Bregman trace* of $(e,a)$ against $(f,b)$ is
--
--   $$
--   \begin{aligned}
--   &\mathrm{SBT}_p(e,a,f,b)\\
--   &\quad=\operatorname{Tr}F_p(\mathrm{diag}_e(a))\\
--   &\qquad-\operatorname{Tr}F_p(\mathrm{diag}_f(b))\\
--   &\qquad-\operatorname{Re}\operatorname{Tr}\!\big(\mathrm{diag}_e(a)\circ G_p(\mathrm{diag}_f(b))\big)\\
--   &\qquad+\operatorname{Tr}\!\big(\mathrm{diag}_f(b)\circ G_p(\mathrm{diag}_f(b))\big)
--   \end{aligned}
--   $$
--
--   (`spectralBregmanTrace`). The first, second and fourth traces are traces of operators diagonal with real entries. The cross term is the real trace of a product of two self-adjoint operators; its reality also follows from $\overline{\operatorname{Tr}(AB)}=\operatorname{Tr}(BA)=\operatorname{Tr}(AB)$. The product itself need not be self-adjoint. Write $\operatorname{ov}(e_i,f_j) = |\langle e_i,f_j\rangle|^2$ for the squared overlap of two basis vectors (`orthonormalBasisOverlap`), and
--
--   $$
--   \beta_p(x,y) \;=\; F_p(x) - F_p(y) - G_p(y)(x-y)
--   $$
--
--   for the scalar Bregman quantity of $F_p$ (`scalarBregman`). The theorem states
--
--   $$
--   \mathrm{SBT}_p(e,a,f,b) \;=\; \sum_{(i,j)\,\in\,\iota\times\kappa} \operatorname{ov}(e_i,f_j)\,\beta_p(a_i,b_j).
--   $$
--
--   This is one of two exact finite double-sum decompositions (the other is for the squared spectral Mazur distance) that let a scalar comparison between $\beta_p(x,y)$ and a Mazur-type quantity, once it is known to hold for every pair of real numbers, be summed against the overlap weights $\operatorname{ov}(e_i,f_j)$ — which are nonnegative and sum to $1$ along every row and column — and so lift unchanged, with the same constants, to a comparison between traces of finite-dimensional Hermitian operators.
--
--   **Formalization Note** The identity holds for every real $p$, including $p\le0$ or $p\in(0,1)$, because $F_p$, $G_p$, and division are all totalized in Lean: $F_p(0)=|0|^p/p$ evaluates to $0$ for every real $p$ (for $p\ne0$ because $0^p=0$; for $p=0$ because $0^0=1$ but $1/0=0$). This theorem asserts an algebraic trace identity, with no nonnegativity conclusion. For $p>1$, $F_p$ is convex and differentiable everywhere with derivative $G_p$, giving the usual Bregman-divergence interpretation used later in the argument.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/HermitianSpectral.lean#L383-L405

import Definitions.Def_HlawkaSchatten_HermitianSpectral
import Definitions.Def_HlawkaSchatten_ScalarBregman
import Definitions.Def_HlawkaSchatten_SpectralLift
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Finite Hermitian spectral trace expansions

This file connects the overlap-weighted scalar comparison to traces of
finite-dimensional symmetric complex-linear maps.
-/


open scoped InnerProductSpace
open RCLike
open ComplexConjugate

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open HlawkaSchatten

theorem HlawkaSchatten.spectralBregmanTrace_eq_sum [FiniteDimensional ℂ E]
    (p : ℝ) (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) :
    spectralBregmanTrace p e a f b =
      ∑ ij : ι × κ, orthonormalBasisOverlap e f ij *
        scalarBregman p (a ij.1) (b ij.2) := by sorry
