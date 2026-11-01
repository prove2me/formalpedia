-- Prove2me | Theorems.Thm_IDEPoA_lemma_2_5
-- name    : IDEPoA.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:23.140132+00:00
-- url     : https://prove2.me/theorems/19ac4aa0-1169-448d-acaf-d23fc7511f32
-- title:
--   Lemma 2.5: $\Xi(f)=\int_0^{\Theta}\theta Z'-\sum_v\int_0^{\theta_0}\theta u_v=\int_0^{\Theta}F^\Delta$
-- statement:
--   For a terminating feasible flow $f$ with makespan $\Theta=\Theta(f)$,
--   $$\Xi(f)=\int_0^{\Theta}\theta\cdot Z'(\theta)\,d\theta-\sum_{v\ne t}\int_0^{\theta_0}\theta\cdot u_v(\theta)\,d\theta=\int_0^{\Theta}F^\Delta(\theta)\,d\theta.$$
--
--   The second form reads the total travel times as the integral over time of the flow volume in the network. It is the form used for the upper bound in Theorem 3.9.
--
--   **Formalization Note** $Z'$ is the density $\sum_{e\in\delta_t^-}f_e^--\sum_{e\in\delta_t^+}f_e^+$ of $Z$, as $Z$ is differentiable only almost everywhere. The value $\Xi(f)$ is in $[0,\infty]$; the statement says that the two real expressions agree and that $\Xi(f)$ equals their common value.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
--   - encoding: Z′(θ) → the density of Z, ∑ fe− over δt− minus ∑ fe+ over δt+; reason: Z is absolutely continuous, so the derivative exists a.e. and equals this density; the integral is the same
--   - encoding: Ξ(f) a real number → Ξ(f) in ℝ≥0∞, equal to ofReal of the real expression; reason: Ξ is a lower integral so that it is defined on every flow; the value is the same for a terminating flow
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, Lemma 2.5, pp.10, 40

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- Lemma 2.5 (Graf & Harks, arXiv:2007.07794v2, pp.10, 40): for a terminating feasible flow,
`Ξ(f) = ∫₀^Θ θ Z′(θ) dθ − ∑_{v ≠ t} ∫₀^θ₀ θ uᵥ(θ) dθ = ∫₀^Θ F^Δ(θ) dθ`.

**Formalization Note.** `Z′` is its density `Zrate` (`Z` is only almost everywhere differentiable).
`Ξ(f)` lives in `ℝ≥0∞`, so the first conjunct is the equality of the two real expressions, the second
identifies `Ξ(f)` with the common value, which is finite and nonnegative. -/
theorem lemma_2_5 (N : FlowNetwork V E) (hN : Standing N) (f : Flow E) (hf : IsFeasible N f)
    (hterm : Terminates N f) :
    ∫ θ in (0 : ℝ)..(makespan N f).toReal, θ * Zrate N f θ
        - ∑ v ∈ Finset.univ.erase N.t, ∫ θ in (0 : ℝ)..N.θ₀, θ * N.u v θ =
      ∫ θ in (0 : ℝ)..(makespan N f).toReal, totalLoad f θ ∧
    totalTravel N f =
      ENNReal.ofReal (∫ θ in (0 : ℝ)..(makespan N f).toReal, totalLoad f θ) := by sorry

end IDEPoA
