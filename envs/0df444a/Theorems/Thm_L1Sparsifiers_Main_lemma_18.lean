-- Prove2me | Theorems.Thm_L1Sparsifiers_Main_lemma_18
-- name    : L1Sparsifiers.Main.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:18.603324+00:00
-- url     : https://prove2.me/theorems/fb0c2a54-87ed-4564-8ea9-a99cc4687b21
-- title:
--   Lemma 18 — nonzero separately convex homogeneous $f\ge0$ is positive on a fraction $e^{-2n}$ of the vertices
-- statement:
--   Let $f:[-1,1]^m\to\mathbb R_{\ge0}$ be separately convex and not identically zero on $[-1,1]^m$, and suppose that
--   $$f(\rho x)=\rho^n f(x)\qquad\text{for all }x\in\{-1,1\}^m\text{ and }0\le\rho\le1 .$$
--   Then
--   $$\mathbb P_{x\sim\{-1,1\}^m}\big[f(x)>0\big]\ge e^{-2n},$$
--   where $x$ is uniform on the $2^m$ vertices of the cube.
--
--   Homogeneity is required only along the rays to the vertices. Nonvanishing is assumed somewhere on the solid cube; separate convexity then implies nonvanishing at some vertex, as the source proves. Corollary 19 transfers the bound to the continuous cube, and Theorem 20 applies it to eroded zonotopes.
--
--   **Formalization Note** $f$ is a total function on $\mathbb R^m$; nonnegativity, separate convexity, nonvanishing and homogeneity are all required on $[-1,1]^m$ only. $\rho^n$ is the real power.
--
--   Differences from the source:
--   - encoding: f : [−1,1]^m → ℝ_{≥0} → a function on ℝ^m, nonnegative and separately convex on [−1,1]^m, nonzero at some point of [−1,1]^m; reason: values outside the cube are never used
--   - generalization: the degree n (the dimension, a natural number, in the paper) → any real n ≥ 0, with ρ^n a real power; reason: the statement for real n ≥ 0 specializes to every natural n
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §4, Lemma 18, p.10

import Mathlib
import Definitions.Def_PSDPolyApprox_expect
import Definitions.Def_L1Sparsifiers_Main_UniformCube
import Definitions.Def_L1Sparsifiers_Main_SeparatelyConvex

namespace L1Sparsifiers.Main

open PSDPolyApprox

/-- **Lemma 18** (p.10). "Let f : [−1,1]^m → ℝ_{≥0} be separately convex and not identically zero
so that f(ρx) = ρⁿ f(x) for all x ∈ {−1,1}^m and 0 ≤ ρ ≤ 1. Then
P_{x∼{−1,1}^m}[f(x) > 0] ≥ e^{−2n}."

`f` is nonnegative and separately convex on `[−1,1]^m`, nonzero at some point of the solid cube,
and homogeneous of degree `n` along the rays to the vertices. The probability is over the uniform
distribution on the `2^m` vertices. The degree `n ≥ 0` is real (`ρⁿ` is `Real.rpow`); the paper
uses it with `n` the dimension, a natural number. -/
theorem lemma_18 {m : ℕ} {n : ℝ} (hn : 0 ≤ n) (f : (Fin m → ℝ) → ℝ) (hnn : ∀ x ∈ cube m, 0 ≤ f x)
    (hsep : SepConvexOn (Set.Icc (-1 : ℝ) 1) f) (hnz : ∃ x ∈ cube m, f x ≠ 0)
    (hhom : ∀ σ : Cube m, ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → f (ρ • vertex σ) = ρ ^ n * f (vertex σ)) :
    Real.exp (-2 * n) ≤ expect (fun σ : Cube m => if 0 < f (vertex σ) then (1 : ℝ) else 0) := by sorry

end L1Sparsifiers.Main
