-- Prove2me | Theorems.Thm_MilnorDynamics_montel_normalized_omitting_zero_one_infty
-- name    : MilnorDynamics.montel_normalized_omitting_zero_one_infty
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T17:59:50.05326+00:00
-- url     : https://prove2.me/theorems/2ed4dd6c-acd8-4511-91c3-7fd2b5919cc3
-- title:
--   Montel's theorem in normalised form - holomorphic maps omitting 0, 1, infinity form a normal family
-- statement:
--   **Montel's theorem, normalised at $0,1,\infty$.** Let $U\subseteq\mathbb C$ be a domain (a nonempty connected open set) and let $\mathcal F$ be a family of maps $U\to\hat{\mathbb C}$ holomorphic in the coordinate-chart sense of `IsHolomorphicOn` such that every $f\in\mathcal F$ omits the three values $0$, $1$ and $\infty$. Then $\mathcal F$ is a normal family: every sequence in $\mathcal F$ has a subsequence converging locally uniformly on $U$ in the chordal metric to a continuous limit map $U\to\hat{\mathbb C}$. This is the analytic core of Milnor's Theorem 3.7 after the three omitted values have been moved to the standard triple by a Mobius transformation; equivalently it is the statement that holomorphic maps into the thrice-punctured sphere form a normal family (Marty's criterion for the hyperbolic three-punctured sphere).
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, Theorem 3.7, pp. 35-36 (Montel's theorem after normalising the three omitted values to 0, 1, infinity); the analytic input is Marty's criterion together with the hyperbolicity of the thrice-punctured sphere.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem montel_normalized_omitting_zero_one_infty (U : Set ℂ) (hU : IsOpen U)
    (hUc : IsConnected U)
    (𝓕 : Set (ℂ → OnePoint ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, IsHolomorphicOn U f ∧
      ∀ z ∈ U, f z ≠ ((0 : ℂ) : OnePoint ℂ) ∧ f z ≠ ((1 : ℂ) : OnePoint ℂ) ∧ f z ≠ ∞) :
    IsNormalFamily U 𝓕 := by sorry

end MilnorDynamics
