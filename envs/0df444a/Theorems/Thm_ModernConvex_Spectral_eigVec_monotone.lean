-- Prove2me | Theorems.Thm_ModernConvex_Spectral_eigVec_monotone
-- name    : ModernConvex.Spectral.eigVec_monotone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:40.396989+00:00
-- url     : https://prove2.me/theorems/abd07cf5-6530-4254-a07e-e949173269bd
-- title:
--   (A) — the eigenvalue vector is ⪰-monotone
-- statement:
--   For a symmetric $m\times m$ matrix $X$ let $\lambda(X) = (\lambda_1(X),\dots,\lambda_m(X))$ be its eigenvalues in nonascending order. If $X$ and $X'$ are symmetric $m\times m$ matrices with $X \succeq X'$, that is, $X - X'$ is positive semidefinite, then
--   $$\lambda_i(X) \ge \lambda_i(X'), \qquad i = 1,\dots,m.$$
--
--   This is the basic fact (A) that the book uses to prove that the sum of the $k$ largest eigenvalues is semidefinite representable (example 18.c). It also appears in the proof of example 18.d.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 148, fact (A) (proved in Exercise 4.5(i))

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR

open Matrix

namespace ModernConvex.Spectral

/-- Ben-Tal–Nemirovski, fact (A), p. 148 (proved in Exercise 4.5(i)): the vector `λ(X)` is a
`⪰`-monotone function of `X ∈ Sᵐ`: `X ⪰ X' ⇒ λ(X) ≥ λ(X')` (coordinatewise). -/
theorem eigVec_monotone {m : ℕ} (X X' : Matrix (Fin m) (Fin m) ℝ) (hX : X.IsHermitian)
    (hX' : X'.IsHermitian) (h : (X - X').PosSemidef) :
    ∀ i : Fin m, eigVec X' i ≤ eigVec X i := by sorry

end ModernConvex.Spectral
