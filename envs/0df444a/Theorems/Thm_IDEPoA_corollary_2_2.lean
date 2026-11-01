-- Prove2me | Theorems.Thm_IDEPoA_corollary_2_2
-- name    : IDEPoA.corollary_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:23.841242+00:00
-- url     : https://prove2.me/theorems/a750f44b-1690-44f4-ad81-cd6f8593f3df
-- title:
--   Corollary 2.2: after $\theta_0$ the total flow volume does not increase
-- statement:
--   Let $f$ be a feasible flow. For all $b\ge a\ge\theta_0$,
--   $$F^\Delta(b)\le F^\Delta(a).$$
--   In particular, if $\hat\theta\ge\theta_0$ and $F^\Delta(\hat\theta)=0$, then $F^\Delta(\theta)=0$ for all $\theta\ge\hat\theta$.
--
--   This makes the makespan meaningful: once the network is empty after the end of the inflow, it stays empty.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, Corollary 2.2, p.9

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- Corollary 2.2 (Graf & Harks, arXiv:2007.07794v2, p.9): after `θ₀` the total flow volume is
non-increasing, and once it is zero at a time `θ̂ ≥ θ₀` it stays zero. -/
theorem corollary_2_2 (N : FlowNetwork V E) (hN : Standing N) (f : Flow E) (hf : IsFeasible N f) :
    (∀ a b : ℝ, N.θ₀ ≤ a → a ≤ b → totalLoad f b ≤ totalLoad f a) ∧
    (∀ θhat : ℝ, N.θ₀ ≤ θhat → totalLoad f θhat = 0 →
      ∀ θ : ℝ, θhat ≤ θ → totalLoad f θ = 0) := by sorry

end IDEPoA
