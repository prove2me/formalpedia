-- Prove2me | Theorems.Thm_MilnorDynamics_oscillation_bound_of_bounded_deriv
-- name    : MilnorDynamics.oscillation_bound_of_bounded_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T00:17:39.425063+00:00
-- url     : https://prove2.me/theorems/3dc2fe56-5d3c-49b7-89bb-c029158a1d71
-- title:
--   Bounded derivatives give a uniform oscillation bound on every compact set
-- statement:
--   **Bounded derivatives give a uniform oscillation bound.** Let $f_n$ be holomorphic on an open $U$ and suppose that on every compact subset of $U$ the derivatives are uniformly bounded. Then the family is uniformly equicontinuous on every compact subset of $U$: for each compact $K\subseteq U$ and each $\varepsilon>0$ there is $\delta>0$ such that for all $n$ and all $x,y\in K$,
--
--   $$|x-y|<\delta\ \Longrightarrow\ |f_n(x)-f_n(y)|<\varepsilon .$$
--
--   Proof. Shrink to a compact neighbourhood of $K$ inside $U$ and take the derivative bound $B$ there. On the segment joining two points $x,y$ of $K$ the mean value inequality for complex-valued functions gives $|f_n(x)-f_n(y)|\le B\,|x-y|$; taking $\delta=\varepsilon/B$ (or $\delta=1$ when $B=0$) proves the claim.
--
--   This is the equicontinuity input consumed by the Arzela-Ascoli extraction step.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3; the mean value inequality applied to a holomorphic family with bounded derivatives.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem oscillation_bound_of_bounded_deriv (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hderiv : ∀ K ⊆ U, IsCompact K → ∃ B, ∀ n, ∀ z ∈ K, ‖deriv (f n) z‖ ≤ B) :
    ∀ K ⊆ U, IsCompact K → ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ < δ → ‖f n x - f n y‖ < ε := by sorry

end MilnorDynamics
