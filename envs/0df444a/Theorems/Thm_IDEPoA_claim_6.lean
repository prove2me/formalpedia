-- Prove2me | Theorems.Thm_IDEPoA_claim_6
-- name    : IDEPoA.claim_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:33.068985+00:00
-- url     : https://prove2.me/theorems/49e8ece8-f8d6-48d7-bd53-f73e7a955cd7
-- title:
--   Claim 6: an edge's travel time as an integral of its rates (corrected: $-\theta f_e^+$ for $+\theta f_e^+$)
-- statement:
--   Let $f$ be a terminating feasible flow with makespan $\Theta=\Theta(f)$ and let $e$ be an edge. Then
--   $$\int_0^{\Theta}c_e(\theta)f_e^+(\theta)\,d\theta=\int_0^{\Theta}\Bigl((\theta+\tau_e)\,f_e^-(\theta+\tau_e)-\theta f_e^+(\theta)\Bigr)\,d\theta.$$
--
--   The identity expresses the travel time spent on one edge through departure and arrival times, and it is the step from which Lemma 2.5 follows by a telescoping sum.
--
--   **Formalization Note** Both integrands are integrable on $[0,\Theta]$, since $c_e$ is continuous and the rates are locally integrable, so that neither side is a junk value.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
--   - correction: ∫ ce fe+ = ∫ (θ + τe) fe−(θ + τe) + θ fe+(θ) dθ (pp.10, 40) → − θ fe+(θ) in place of + θ fe+(θ); reason: the printed sign is false: on one edge st with τ = ν = 1, inflow 1 on [0,1), θ0 = 1, the left side is 1 and the printed right side is 2; the last line of the paper's proof (p.41) has −
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, Claim 6, p.40, also p.10; last line of its proof, p.41

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- Claim 6 (Graf & Harks, arXiv:2007.07794v2, App. B, p.40; also p.10), corrected: for a
terminating feasible flow and every edge,
`∫₀^Θ cₑfₑ⁺ dθ = ∫₀^Θ ((θ + τₑ) fₑ⁻(θ + τₑ) − θ fₑ⁺(θ)) dθ`.

The page prints `+ θ fₑ⁺(θ)`; the last line of its proof on p.41 has `−`, and the printed sign is
false on the one-edge network (`IDEPoA_oneEdge.lean`).

**Formalization Note.** Both integrands are integrable on `[0, Θ]`: `cₑ` is continuous, and `fₑ⁺`,
`fₑ⁻` are integrable on bounded intervals by feasibility. `Θ` is the real value of the makespan,
finite as `f` terminates. -/
theorem claim_6 (N : FlowNetwork V E) (hN : Standing N) (f : Flow E) (hf : IsFeasible N f)
    (hterm : Terminates N f) (e : E) :
    ∫ θ in (0 : ℝ)..(makespan N f).toReal, cost N f e θ * f.fplus e θ =
      ∫ θ in (0 : ℝ)..(makespan N f).toReal,
        ((θ + N.τ e) * f.fminus e (θ + N.τ e) - θ * f.fplus e θ) := by sorry

end IDEPoA
