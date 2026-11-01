-- Prove2me | Theorems.Thm_IDEPoA_theorem_3_9
-- name    : IDEPoA.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:14.633032+00:00
-- url     : https://prove2.me/theorems/5c8f3439-5eaf-4f03-8f49-7cc7cc3d9567
-- title:
--   Theorem 3.9: termination and total travel time bounds for IDE flows
-- statement:
--   Let $\mathcal N$ be a single-sink network with total flow volume $U$. Every IDE flow $f$ terminates before
--   $$\hat\theta=\theta_0+2U\sum_{e\in E}\Bigl(\tau_e+\frac1{2\nu_e}\Bigr)+\tau(P_{\max})+\frac12$$
--   and has total travel times of at most
--   $$\lceil3U\rceil\,U\Bigl(2\tau(P_{\max})+\sum_{e\in E}\Bigl(\tau_e+\frac1{2\nu_e}\Bigr)+1\Bigr).$$
--
--   This is the first explicit termination bound for IDE flows. Here $U$ is a real number.
--
--   Differences from the source:
--   - generalization: directed graph G = (V, E) with edges vw → finite directed multigraph with tail and head maps, loops and parallel edges allowed; reason: a simple digraph is a special case
--   - reading: f+, f- integrable functions (p.7) → f+, f- integrable on every [0, T]; reason: F+ and F- only need the integral on [0, θ]; global integrability would exclude forever-cycling flows up front, and local integrability contains it
--   - encoding: rates on R≥0, constraints for θ ∈ R≥0 → rates ℝ → ℝ, constraints quantified over 0 ≤ θ; reason: values at negative times play no role
--   - encoding: node labels defined by the recursion (6) → label as the infimum of the costs of v-t walks; reason: same function for a feasible flow; the recursion is proved in a verification file
--   - reading: τ(Pmax), the physical length of a longest v-t path → supremum of the lengths of simple v-t paths over all nodes v; reason: the only reading that is finite on a cyclic graph; on an acyclic graph every walk is simple
--   - reading: terminates before θ̂ → strict inequality Θ(f) < θ̂ in ℝ≥0∞; reason: the proof gives Θ(f) < θ̃ + τ(Pmax) + 1/2 ≤ θ̂
--   - encoding: total travel times of a terminating flow → Ξ(f) in ℝ≥0∞, for every IDE flow; reason: termination is the first clause, so Ξ is the paper's on these flows
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, Theorem 3.9, p.21

import Mathlib
import Definitions.Def_IDEPoA_Model

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- Theorem 3.9 (Graf & Harks, arXiv:2007.07794v2, p.21): every IDE flow terminates before
`θ̂ = θ₀ + 2U ∑ₑ (τₑ + 1/(2νₑ)) + τ(Pmax) + 1/2` and has total travel times of at most
`⌈3U⌉ U (2τ(Pmax) + ∑ₑ (τₑ + 1/(2νₑ)) + 1)`. Here `U` is the real total flow volume. -/
theorem theorem_3_9 (N : FlowNetwork V E) (hN : Standing N) (f : Flow E) (hf : IsIDE N f) :
    makespan N f <
        ENNReal.ofReal (N.θ₀ + 2 * totalVolume N * weightSum N + tauPmax N + 1 / 2) ∧
      totalTravel N f ≤
        ENNReal.ofReal
          ((⌈3 * totalVolume N⌉₊ : ℝ) * totalVolume N * (2 * tauPmax N + weightSum N + 1))
    := by sorry

end IDEPoA
