-- Prove2me | Theorems.Thm_JHolomorphic_exists_norm_sub_le_pow_of_iteratedFDeriv_eq
-- name    : JHolomorphic.exists_norm_sub_le_pow_of_iteratedFDeriv_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T14:39:02.829277+00:00
-- url     : https://prove2.me/theorems/42b8c62a-8758-4b92-b11e-daf1d0dd8784
-- title:
--   Agreement of all derivatives at a point gives faster-than-polynomial decay of the difference
-- statement:
--   Let $F$ be a real normed vector space, let $r>0$, and let $u,v:\mathbb{C}\to F$ be $C^\infty$ on the disc $D_r=\{|z|<r\}$, where $\mathbb{C}$ is viewed as a real normed space. Suppose that the derivatives of all orders of $u$ and $v$ at $0$ coincide:
--   $$D^m u(0)=D^m v(0)\qquad\text{for every } m\in\mathbb{N}$$
--   (including $m=0$, i.e. $u(0)=v(0)$). Then for every $N\in\mathbb{N}$ there are constants $C\in\mathbb{R}$ and $\delta>0$ with
--   $$\|u(z)-v(z)\|\le C\,|z|^N\qquad(|z|<\delta).$$
--
--   This converts agreement of all derivatives at a point into quantitative decay of the difference faster than every power, the form in which infinite-order contact is used in unique-continuation arguments.
--
--   **Formalization Note** $D^m u(0)$ is `iteratedFDeriv ℝ m u 0`, the iterated real Fréchet derivative of $u$ as a map on all of $\mathbb{C}$; since $u$ is `ContDiffOn ℝ ∞` on the open disc `ball 0 r`, these are the usual derivatives at $0$. The conclusion is `∀ N : ℕ, ∃ C δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ, ‖u z - v z‖ ≤ C * ‖z‖ ^ N`; no relation between $\delta$ and $r$ is asserted.
-- source:
--   Standard calculus; used in C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Proposition 2.28

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic

namespace JHolomorphic

open Metric Filter Topology
open scoped ContDiff

/-- Two maps that are `C^∞` on a disc around `0` and whose derivatives of all orders agree at `0`
differ by at most `C ‖z‖ ^ N` near `0`, for every `N`. -/
theorem exists_norm_sub_le_pow_of_iteratedFDeriv_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (r : ℝ) (hr : 0 < r) (u v : ℂ → F)
    (hu : ContDiffOn ℝ ∞ u (ball 0 r)) (hv : ContDiffOn ℝ ∞ v (ball 0 r))
    (hD : ∀ m : ℕ, iteratedFDeriv ℝ m u 0 = iteratedFDeriv ℝ m v 0) :
    ∀ N : ℕ, ∃ C δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (0 : ℂ) δ, ‖u z - v z‖ ≤ C * ‖z‖ ^ N := by
  sorry

end JHolomorphic
