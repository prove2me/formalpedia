-- Prove2me | Theorems.Thm_OAI_ContinuumTemperature_main_theorem
-- name    : OAI.ContinuumTemperature.main_theorem
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:29.03309+00:00
-- url     : https://prove2.me/theorems/75b332f1-7e9a-4f74-a514-7b896dd1476b
-- statement:
--   The theorem states that the defined proposition MainStatement holds, an existence claim about a classical gas of particles in three-dimensional Euclidean space interacting through a radial pair potential φ, where the potential between two particles at x and y is φ(‖x−y‖) and is +∞ at coincident points, and the energy of N points is the sum of the pair potentials over all pairs i<j. It asserts that there exist a function φ, a function f of (β,ρ), an open, order-connected (interval-like), nonempty set I contained in (0,∞), and a number βc strictly between 1/2 and 3/2 such that the following hold. First, φ is admissible: the radial potential is measurable; φ is bounded above and below on every compact interval [a,b] with 0<a≤b; φ tends to +∞ as r decreases to 0; φ≤−a<0 on some interval [r₁,r₂] with 0<r₁<r₂; r²|φ(r)| is integrable on (R,∞) for some R>0; and there is a constant B with energy at least −BN for every N and every configuration of N points. Second, φ(r) is little-o of r⁻³ as r tends to infinity. Third, f is the canonical free energy of φ: for every β>0 and ρ>0, L⁻³ log Z tends to −β f(β,ρ) as L→∞, where Z is the partition function for ⌊ρL³⌋ particles in the cube [−L/2,L/2]³, namely (1/N!) times the integral over that cube of the Boltzmann weight, which is exp(−β·energy) and is 0 when the energy is +∞. Fourth, for every ρ in I, the map β↦f(β,ρ) has a left derivative dminus and a right derivative dplus at βc, both existing as one-sided derivatives, with dplus<dminus, so the graph has a kink at βc.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ContinuumTransition.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ContinuumTransition.lean; bytes 2299..2349
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ContinuumTransition

namespace OAI

open scoped Topology BigOperators ENNReal

open Filter MeasureTheory Set

namespace ContinuumTemperature

theorem main_theorem : MainStatement := by
  sorry

end ContinuumTemperature
end OAI
