-- Prove2me | Theorems.Thm_JHolomorphic_eventuallyEq_zero_of_forall_norm_le_pow
-- name    : JHolomorphic.eventuallyEq_zero_of_forall_norm_le_pow
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T14:34:52.567165+00:00
-- url     : https://prove2.me/theorems/c5ef08d6-de14-4e73-a3b6-e6be4139048b
-- title:
--   A holomorphic map with a zero of infinite order vanishes near that point
-- statement:
--   Let $F$ be a complex Banach space, let $r>0$, and let $f:\mathbb{C}\to F$ be holomorphic on the disc $D_r=\{|z|<r\}$. Suppose that $f$ vanishes to infinite order at $0$ in the sense that for every $N\in\mathbb{N}$ there are constants $C\in\mathbb{R}$ and $\delta>0$ with
--   $$\|f(z)\|\le C\,|z|^N\qquad(|z|<\delta).$$
--   Then $f=0$ on a neighbourhood of $0$.
--
--   This is the holomorphic form of unique continuation from a point: a holomorphic map cannot decay faster than every power at a point unless it vanishes nearby.
--
--   **Formalization Note** Holomorphy is `DifferentiableOn ℂ f (ball 0 r)`; the hypothesis is `∀ N : ℕ, ∃ C δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ, ‖f z‖ ≤ C * ‖z‖ ^ N`; the conclusion is `f =ᶠ[𝓝 0] 0`. No size of the neighbourhood is asserted.
-- source:
--   Standard complex analysis; used in C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Proposition 2.28

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace JHolomorphic

open Metric Filter Topology

/-- A holomorphic map `f` on a disc around `0` such that for every `N` there is a bound
`‖f z‖ ≤ C ‖z‖ ^ N` near `0` vanishes on a neighbourhood of `0`. -/
theorem eventuallyEq_zero_of_forall_norm_le_pow {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] (r : ℝ) (hr : 0 < r) (f : ℂ → F)
    (hf : DifferentiableOn ℂ f (ball 0 r))
    (hb : ∀ N : ℕ, ∃ C δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (0 : ℂ) δ, ‖f z‖ ≤ C * ‖z‖ ^ N) :
    f =ᶠ[𝓝 0] 0 := by
  sorry

end JHolomorphic
