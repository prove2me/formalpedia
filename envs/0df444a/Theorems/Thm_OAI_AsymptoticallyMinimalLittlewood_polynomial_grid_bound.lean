-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_polynomial_grid_bound
-- name    : OAI.AsymptoticallyMinimalLittlewood.polynomial_grid_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:51:56.795253+00:00
-- url     : https://prove2.me/theorems/7c0762e2-44c3-400b-98bc-cfdb6fd13b10
-- title:
--   A polynomial of degree less than $N$ bounded by $G$ at the $M$-th roots of unity, $M\ge 2N$, is bounded by $2G$ on the unit circle
-- statement:
--   Let $N\ge 1$ and $M$ be integers with $2N\le M$, and let $\omega_j=e^{2\pi i j/M}$ for $j\in\mathbb{Z}/M\mathbb{Z}$. Let $c_0,\dots,c_{N-1}\in\mathbb{C}$ and $P(z)=\sum_{k=0}^{N-1}c_kz^{k}$. Let $G\ge 0$ and suppose that $|P(\omega_j)|\le G$ for every $j\in\mathbb{Z}/M\mathbb{Z}$, that is, at every $M$-th root of unity. Then
--
--   $$
--   |P(z)|\le 2G\qquad\text{for every }z\in\mathbb{C}\text{ with }|z|=1 .
--   $$
--
--   So sampling a polynomial of degree less than $N$ at $M\ge 2N$ equally spaced points of the unit circle determines its supremum norm on the circle up to the absolute factor $2$, with no logarithmic loss in $N$. In the rounding to Littlewood polynomials this transfers an error bound proved on a finite grid of roots of unity to the whole circle.
--
--   **Formalization Note** The coefficients are indexed by `Fin N`, $\omega_j$ is `ZMod.stdAddChar j`, and $M\ge 1$ is the instance `NeZero M` (implied here by $2N\le M$ and $N\ge 1$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L1165-L1220

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff
open scoped ComplexConjugate
open Finset

theorem OAI.AsymptoticallyMinimalLittlewood.polynomial_grid_bound {N M : ℕ} [NeZero M] (hN : 0 < N) (hNM : 2 * N ≤ M)
    (c : Fin N → ℂ) {G : ℝ} (hG : 0 ≤ G)
    (hgrid : ∀ j : ZMod M, ‖∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)‖ ≤ G)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖∑ k : Fin N, c k * z ^ (k : ℕ)‖ ≤ 2 * G := by sorry
