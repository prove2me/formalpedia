-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_latticeSample_finite_support
-- name    : OAI.EuclideanRamsey.latticeSample_finite_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:09:02.31824+00:00
-- url     : https://prove2.me/theorems/7bd434ba-002d-4666-8f00-6e742af9337f
-- title:
--   A compactly supported function sampled on $\tfrac1n\mathbb{Z}^k$ has only finitely many nonzero samples
-- statement:
--   Let $k\in\mathbb{N}$, let $n$ be a positive integer, and let $f:\mathbb{R}^k\to\mathbb{R}$ be a function with compact support (no continuity is assumed). For $\gamma\in\mathbb{Z}^k$ write $\gamma/n=(\gamma_1/n,\dots,\gamma_k/n)$. Then only finitely many lattice points give a nonzero sample:
--
--   $$
--   \#\big\{\gamma\in\mathbb{Z}^k:\ f(\gamma/n)\neq0\big\}<\infty .
--   $$
--
--   Hence $\gamma\mapsto f(\gamma/n)$ is a finitely supported real function on $\mathbb{Z}^k$, and every lattice sum built from it is a finite sum. This is used to turn a smooth bump into a finitely supported discrete kernel on the lattice.
--
--   **Formalization Note** Compact support means that `tsupport f`, the closure of $\{x:f(x)\neq0\}$, is compact. The conclusion is `Function.HasFiniteSupport (fun γ : Fin k → ℤ => f (latticeSample n γ))`, where `latticeSample n γ` is the point $\gamma/n$, and the hypothesis on $n$ is `n ≠ 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Discretization.lean#L190-L214

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
universe uDomain uIndex
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open MeasureTheory
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter

theorem OAI.EuclideanRamsey.latticeSample_finite_support {k n : ℕ} (hn : n ≠ 0)
    {f : (Fin k → ℝ) → ℝ} (hf : HasCompactSupport f) :
    Function.HasFiniteSupport (fun γ : Fin k → ℤ => f (latticeSample n γ)) := by sorry
