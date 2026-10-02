-- Prove2me | Theorems.Thm_MilnorDynamics_schottky_bound
-- name    : MilnorDynamics.schottky_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-01T14:56:15.644867+00:00
-- url     : https://prove2.me/theorems/ad33741e-481a-4525-99b8-e0a869d94af0
-- title:
--   Schottky bound: a holomorphic function on the disc omitting 0 and 1 is controlled on every smaller disc by its value at the centre
-- statement:
--   **Schottky's bound.** There is a constant $C = C(M, r)$ depending only on $M \ge 0$ and on a radius $0 \le r < 1$ such that every holomorphic $g$ on the open unit disc with values in $\mathbb C \setminus \{0,1\}$ and with $|g(0)| \le M$ satisfies $|g(z)| \le C$ for all $|z| \le r$.
--
--   This is Schottky's theorem in the form used by the escape step of Milnor's proof of Montel's theorem (Milnor, *Dynamics in One Complex Variable*, 3rd ed., Section 3): it is exactly the rigidity that a family of holomorphic functions omitting two values cannot be bounded at one point without being bounded on a neighbourhood, with a modulus. The bound is uniform in the function once the centre value is bounded, which is what makes the escape argument work for a whole family at once.
--
--   Equivalent quantitative content: the hyperbolic (Poincare) metric of $\mathbb C \setminus \{0,1\}$ pushes forward along $g$ and is contracted by the Schwarz-Pick lemma, so the position of $g(z)$ is controlled by that of $g(0)$ together with $r$. In particular this statement implies the qualitative rigidity `MilnorDynamics.locally_bounded_of_bounded_at_point`.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3 (escape step in the proof of Montel's theorem), where the rigidity of families omitting two values is Schottky's theorem. Classical form of Schottky's theorem: for f holomorphic on the unit disc omitting 0 and 1, |f(z)| is bounded on |z| <= r < 1 by a constant depending only on |f(0)| and r.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem schottky_bound (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball 0 1) →
      MapsTo g (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) → ‖g 0‖ ≤ M →
      ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ C := by sorry

end MilnorDynamics
