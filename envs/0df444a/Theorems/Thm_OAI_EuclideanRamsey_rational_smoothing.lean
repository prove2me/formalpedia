-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_rational_smoothing
-- name    : OAI.EuclideanRamsey.rational_smoothing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:13:22.502859+00:00
-- url     : https://prove2.me/theorems/25a05b33-ae69-4750-b655-efa71fad5ff7
-- title:
--   Rational smoothing of a lattice stencil: same coset and moment constraints, arbitrarily small weighted negative part
-- statement:
--   Let $k,d,s\in\mathbb N$ with $d\ge1$. Write $\mathbb Q[\mathbb Z^k]$ for the group algebra of $\mathbb Z^k$ over $\mathbb Q$: its elements are finitely supported functions $\nu:\mathbb Z^k\to\mathbb Q$, multiplied by convolution $(\nu\mu)(\delta)=\sum_{\gamma}\nu(\gamma)\,\mu(\delta-\gamma)$. For $\nu\in\mathbb Q[\mathbb Z^k]$ define its mass, first moments and second moments
--   $$m(\nu)=\sum_{\gamma\in\mathbb Z^k}\nu(\gamma),\qquad m_j(\nu)=\sum_{\gamma}\nu(\gamma)\,\gamma_j,\qquad m_{jl}(\nu)=\sum_{\gamma}\nu(\gamma)\,\gamma_j\gamma_l\qquad(1\le j,l\le k),$$
--   and, for a subgroup $\Lambda\le\mathbb Z^k$, its coset pushforward $\pi_\Lambda\nu:\mathbb Z^k/\Lambda\to\mathbb Q$, $\ \pi_\Lambda\nu(\gamma+\Lambda)=\sum_{\delta\in\gamma+\Lambda}\nu(\delta)$. For a real $d\times k$ matrix $U$ let $W_U(x)=\sum_{a=1}^d\bigl(\sum_{j}U_{aj}x_j\bigr)^2=|Ux|^2$ for $x\in\mathbb R^k$.
--
--   Let $\Lambda_1,\dots,\Lambda_s$ be subgroups of $\mathbb Z^k$, let $C$ be a symmetric rational $k\times k$ matrix, and let $U$ be a real $d\times k$ matrix with $UCU^{\top}=I_d$. Suppose $\nu\in\mathbb Q[\mathbb Z^k]$ satisfies $\pi_{\Lambda_i}\nu=0$ for every $i$, $m(\nu)=0$, $m_j(\nu)=0$ for every $j$, and $m_{jl}(\nu)=C_{jl}$ for all $j,l$. Then for every real $\eta>0$ there exist an integer $n\ge1$, an element $\mu\in\mathbb Q[\mathbb Z^k]$ and a rational number $\zeta>0$ such that:
--
--   1. $\pi_{\Lambda_i}\mu=0$ for every $i$;
--   2. $m(\mu)=0$ and $m_j(\mu)=0$ for every $j$;
--   3. $m_{jl}(\mu)/n^2=\zeta\,C_{jl}$ for all $j,l$;
--   4. the weighted negative part of $\mu$ is small:
--   $$\sum_{\delta\in\mathbb Z^k}\max\bigl(-\mu(\delta),\,0\bigr)\,W_U\Bigl(\frac{\delta}{n}\Bigr)<\eta\,\zeta .$$
--
--   So all algebraic constraints on $\nu$ survive (vanishing coset sums, vanishing mass and first moments, second moments proportional to $C$ once the lattice is rescaled by $1/n$), while the negative mass of $\mu$, weighted by $|U\delta/n|^2$, becomes arbitrarily small compared with the scale $\zeta$ of its second moments. This near-positivity is what later lets the signed measure $\mu$ be split into two almost matching families of affine rows, leading to a two-scale embedding of the configuration.
--
--   **Formalization Note** $\mathbb Q[\mathbb Z^k]$ is `LatticeRing k = AddMonoidAlgebra ℚ (Fin k → ℤ)`; $m$, $m_j$, $m_{jl}$, $\pi_\Lambda$ are `mass`, `firstMoment`, `secondMoment`, `cosetPushforward`; $W_U$ is `gradientWeight U` and $\delta/n$ is `latticeSample n δ`. The product $UCU^{\top}$ is formed after casting the entries of $C$ to real numbers. The sum in item 4 is a `tsum` over $\mathbb Z^k$ with only finitely many nonzero terms.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/StencilConvolution.lean#L266-L308

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization

open OAI OAI.EuclideanRamsey
universe uIndex
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped BigOperators

theorem OAI.EuclideanRamsey.rational_smoothing {k d s : ℕ} (hd : 1 ≤ d)
    (Λ : Fin s → AddSubgroup (Lattice k)) (ν : LatticeRing k)
    (C : Matrix (Fin k) (Fin k) ℚ) (U : Matrix (Fin d) (Fin k) ℝ)
    (hC : C.IsSymm) (hU : U*(C.map (Rat.cast : ℚ → ℝ))*U.transpose = (1 : Matrix (Fin d) (Fin d) ℝ))
    (hcos : ∀ i,cosetPushforward (Λ i) ν = 0)
    (hzero : mass ν = 0) (hfirst : ∀ j,firstMoment ν j = 0)
    (hsecond : ∀ j l,secondMoment ν j l = C j l)
    (η : ℝ) (hη : 0 < η) :
    ∃ (n : ℕ) (μ : LatticeRing k) (ζ : ℚ), 1 ≤ n ∧ 0 < ζ ∧
      (∀ i,cosetPushforward (Λ i) μ = 0) ∧ mass μ = 0 ∧
      (∀ j,firstMoment μ j = 0) ∧
      (∀ j l,secondMoment μ j l/(n:ℚ)^2 = ζ*C j l) ∧
      (∑' δ : Lattice k,max (-(μ.coeff δ:ℝ)) 0*gradientWeight U (latticeSample n δ)) < η*ζ := by sorry
