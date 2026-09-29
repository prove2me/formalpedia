-- Prove2me | Theorems.Thm_HlawkaSchatten_spectralMazurDistanceSq_eq_sum
-- name    : HlawkaSchatten.spectralMazurDistanceSq_eq_sum
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:25:14.855882+00:00
-- url     : https://prove2.me/theorems/c72cdb43-f35c-4904-9363-194b8b032576
-- title:
--   The spectral Mazur distance squared as an overlap-weighted sum of scalar Mazur terms
-- statement:
--   Fix a finite-dimensional complex inner-product space $E$ and a real number $p$ (no hypothesis is placed on $p$). Let $(e_i)_{i\in\iota}$ and $(f_j)_{j\in\kappa}$ be orthonormal bases of $E$ indexed by finite index types $\iota,\kappa$, with real numbers $a:\iota\to\mathbb R$, $b:\kappa\to\mathbb R$ attached to them. Write $\mathrm{diag}_e(c)$ for the self-adjoint operator on $E$ with $\mathrm{diag}_e(c)\,e_i=c_i\,e_i$ (`spectralDiagonal`), and for $h:\mathbb R\to\mathbb R$ write $h(c)$ for the tuple $i\mapsto h(c_i)$.
--
--   Let $\psi_p(x) = \operatorname{sign}(x)\,|x|^{p/2}$ for $x\ne0$, with $\psi_p(0)=0$, be the scalar Mazur map (`scalarMazur`). The *spectral Mazur distance squared* of $(e,a)$ against $(f,b)$ is
--
--   $$
--   \begin{aligned}
--   \mathrm{SMD}_p(e,a,f,b)
--   &= \operatorname{Re}\operatorname{Tr}\big(\mathrm{diag}_e(\psi_p(a)^2)\big) \\
--   &\quad - 2\operatorname{Re}\operatorname{Tr}\!\big(\mathrm{diag}_e(\psi_p(a))\circ \mathrm{diag}_f(\psi_p(b))\big) \\
--   &\quad + \operatorname{Re}\operatorname{Tr}\big(\mathrm{diag}_f(\psi_p(b)^2)\big).
--   \end{aligned}
--   $$
--
--   This is the real-valued definition `spectralMazurDistanceSq`. With $\operatorname{ov}(e_i,f_j)=|\langle e_i,f_j\rangle|^2$ the squared overlap of two basis vectors (`orthonormalBasisOverlap`), the theorem states
--
--   $$
--   \mathrm{SMD}_p(e,a,f,b) \;=\; \sum_{(i,j)\,\in\,\iota\times\kappa} \operatorname{ov}(e_i,f_j)\,\big(\psi_p(a_i)-\psi_p(b_j)\big)^2.
--   $$
--
--   This is the second of two exact finite double-sum decompositions (the other is for the trace-level Bregman divergence) that let a scalar comparison known for every pair of real numbers be lifted, with the overlap weights $\operatorname{ov}(e_i,f_j)$ — nonnegative and summing to $1$ along every row and column — unchanged in its constants, to a comparison between traces of finite-dimensional Hermitian operators.
--
--   **Formalization Note** The identity holds for every real $p$ and needs no hypothesis on it: both sides are already expressed through the fully totalized real power $\psi_p$, and the right-hand side is manifestly a sum of squares whatever the sign or size of $p$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/HermitianSpectral.lean#L426-L446

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

theorem HlawkaSchatten.spectralMazurDistanceSq_eq_sum [FiniteDimensional ℂ E]
    (p : ℝ) (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) :
    spectralMazurDistanceSq p e a f b =
      ∑ ij : ι × κ, orthonormalBasisOverlap e f ij *
        (scalarMazur p (a ij.1) - scalarMazur p (b ij.2)) ^ 2 := by sorry
