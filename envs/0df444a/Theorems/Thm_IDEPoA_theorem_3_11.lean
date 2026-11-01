-- Prove2me | Theorems.Thm_IDEPoA_theorem_3_11
-- name    : IDEPoA.theorem_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:25.120918+00:00
-- url     : https://prove2.me/theorems/3b5eb09f-f4c8-4c9b-b655-b8de25ff1dc6
-- title:
--   Theorem 3.11: $\mathrm{M\text{-}PoA}(U,\tau)\le6U\tau$ and $\mathrm{T\text{-}PoA}(U,\tau)\le14U\tau$
-- statement:
--   For all integers $U,\tau\ge1$, the makespan and total travel times prices of anarchy of instantaneous dynamic equilibria over the single-sink instances with total flow volume $U$ and total edge length $\tau$ satisfy
--   $$\mathrm{M\text{-}PoA}(U,\tau)\le6\,U\tau,\qquad\mathrm{T\text{-}PoA}(U,\tau)\le14\,U\tau.$$
--
--   This implies the printed statement $\mathrm{M\text{-}PoA}(U,\tau),\mathrm{T\text{-}PoA}(U,\tau)\in\mathcal O(U\tau)$ in the sense of footnote 1 of the paper, with $k=14$ and $U_0=\tau_0=1$. It is the first upper bound on the price of anarchy of IDE flows, for both objectives.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
--   - encoding: node labels defined by the recursion (6) → label as the infimum of the costs of v-t walks; reason: same function for a feasible flow; the recursion is proved in a verification file
--   - generalization: M-PoA(U, τ), T-PoA(U, τ) ∈ O(Uτ), i.e. there are k, U0, τ0 with f(U, τ) ≤ k Uτ for U ≥ U0, τ ≥ τ0 (footnote 1) → the bounds 6Uτ and 14Uτ for all U, τ ≥ 1; reason: gives footnote 1 with k = 14, U0 = τ0 = 1
--   - reading: any pair of integers (U, τ) → 1 ≤ U and 1 ≤ τ; reason: footnote 1 defines O on N* × N*; at U = 0 the ratio can be 0/0
--   - encoding: N an instance (a finite network) → a structure Instance bundling finite types V, E : Type with a network satisfying the standing assumptions; reason: every finite network is isomorphic to one on such types, and the ratios are invariant under isomorphism
--   - generalization: ΞOPT := inf { Ξ(f) | f a feasible flow }, with Ξ(f) of Definition 2.4 stated for terminating flows → infimum over all feasible flows of the formula of Definition 2.4 as a lower integral; reason: the infimum is at most the one over terminating flows, so the Lean bound implies the bound under either reading
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, Theorem 3.11, p.22, with footnote 1, p.4

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

/-- Theorem 3.11 (Graf & Harks, arXiv:2007.07794v2, p.22) with explicit constants: for all integers
`U, τ ≥ 1`, `M-PoA(U, τ) ≤ 6Uτ` and `T-PoA(U, τ) ≤ 14Uτ`.

This gives the printed `M-PoA(U, τ), T-PoA(U, τ) ∈ O(Uτ)` in the sense of footnote 1, p.4, with
`k = 14`, `U₀ = τ₀ = 1`. -/
theorem theorem_3_11 (U τ : ℕ) (hU : 1 ≤ U) (hτ : 1 ≤ τ) :
    MPoA U τ ≤ 6 * (U : ℝ≥0∞) * (τ : ℝ≥0∞) ∧ TPoA U τ ≤ 14 * (U : ℝ≥0∞) * (τ : ℝ≥0∞) := by sorry

end IDEPoA
