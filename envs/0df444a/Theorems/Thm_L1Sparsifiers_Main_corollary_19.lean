-- Prove2me | Theorems.Thm_L1Sparsifiers_Main_corollary_19
-- name    : L1Sparsifiers.Main.corollary_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:07.891484+00:00
-- url     : https://prove2.me/theorems/bf4ce658-27b0-4e61-ac3a-999811702a2b
-- title:
--   Corollary 19 — the same bound $e^{-2n}$ for $x$ uniform on the solid cube
-- statement:
--   Let $f:[-1,1]^m\to\mathbb R_{\ge0}$ be separately convex with
--   $$f(\rho x)=\rho^n f(x)\qquad\text{for all }x\in[-1,1]^m\text{ and }0\le\rho\le1,$$
--   and assume that $f(x)>0$ for every $x\in[-1,1]^m$ with all coordinates negative. Then
--   $$\mathbb P_{x\sim[-1,1]^m}\big[f(x)>0\big]\ge e^{-2n},$$
--   where $x$ is uniform on the solid cube.
--
--   Theorem 20 applies this to the volume left after eroding a zonotope by a randomly rescaled copy.
--
--   **Formalization Note** $f$ is a total function on $\mathbb R^m$ with all hypotheses required on $[-1,1]^m$; the probability is normalized Lebesgue measure on the cube (outer measure if the event were not measurable).
--
--   Differences from the source:
--   - encoding: f : [−1,1]^m → ℝ_{≥0} → a function on ℝ^m with nonnegativity, separate convexity and homogeneity required on [−1,1]^m; reason: values outside the cube are never used
--   - reading: f strictly positive on the orthant ℝ^m_{<0} → 0 < f x for every x ∈ [−1,1]^m with all x_i < 0; reason: f is only defined on [−1,1]^m, so the orthant is read inside that domain
--   - encoding: P_{x∼[−1,1]^m}[f(x) > 0] → Vol_m({f > 0} ∩ [−1,1]^m)/2^m with Lebesgue outer measure; reason: the event is null-measurable (a separately convex function is continuous on the open cube and the boundary is null), so outer measure and measure agree
--   - generalization: the degree n (a natural number in the paper) → any real n ≥ 0, with ρ^n a real power; reason: specializes to every natural n
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §4, Corollary 19, pp.10–11

import Mathlib
import Definitions.Def_L1Sparsifiers_Main_UniformCube
import Definitions.Def_L1Sparsifiers_Main_SeparatelyConvex

namespace L1Sparsifiers.Main

/-- **Corollary 19** (p.10). "Let f : [−1,1]^m → ℝ_{≥0} be separately convex so that
f(ρx) = ρⁿ f(x) for all x ∈ [−1,1]^m and 0 ≤ ρ ≤ 1. Assume that f is strictly positive on the
orthant ℝ^m_{<0}. Then P_{x∼[−1,1]^m}[f(x) > 0] ≥ e^{−2n}."

The orthant is read inside `f`'s domain: `f > 0` at every `x ∈ [−1,1]^m` with all coordinates
negative. The probability is the continuous uniform distribution on the solid cube. The degree `n ≥ 0` is real (`ρⁿ` is `Real.rpow`); the
paper uses it with `n` a natural number. -/
theorem corollary_19 {m : ℕ} {n : ℝ} (hn : 0 ≤ n) (f : (Fin m → ℝ) → ℝ) (hnn : ∀ x ∈ cube m, 0 ≤ f x)
    (hsep : SepConvexOn (Set.Icc (-1 : ℝ) 1) f)
    (hhom : ∀ x ∈ cube m, ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → f (ρ • x) = ρ ^ n * f x)
    (hpos : ∀ x ∈ cube m, (∀ i, x i < 0) → 0 < f x) :
    Real.exp (-2 * n) ≤ cubeProb m {x | 0 < f x} := by sorry

end L1Sparsifiers.Main
