-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_lemma_4_2
-- name    : InducedExpanderTest989.Structural.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:19.665326+00:00
-- url     : https://prove2.me/theorems/e3e7b8d2-5fa0-445c-848c-b4fe2e67dae0
-- title:
--   Lemma 4.2 — integrability of trace times
-- statement:
--   Let G have maximum degree at most d≥1. Let U contain at least two vertices and have positive inner conductance, and let C_U be its connected component. Write P for the lazy graph walk, P^U for its trace matrix on U, π_U for the uniform law on U, and τ_i for the time of its ith trace visit with τ₀=0.
--   For every z∈C_U, the hitting time T_z^U of U for the walk started at z has finite expectation. Also, for every x∈U and i≥1,
--   $$\mathbb E_z[T_z^U]<\infty,\qquad \mathbb E_x[\tau_i]<\infty.$$
--   Expectations are nonnegative extended integrals, so these assertions cannot be satisfied by replacing an infinite expectation with zero.
--
--   Differences from the source:
--   - encoding: vertices [n], slots [d], null symbol ⊥ → Fin n, zero-based Fin d slots, none; reason: renumbering preserves every adjacency list and graph
--   - encoding: walk trajectories, infinite hitting times and expectations → Ionescu–Tulcea path measure, ℕ∞ visit times and extended nonnegative expectations; reason: never-hit paths retain infinity; real expectations are used only where Lemma 4.2 guarantees finiteness
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.17 (PDF p.19), Lemma 4.2; §4.2.1 standing preamble p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem lemma_4_2 {n d : ℕ} (hd : 1 ≤ d) (G : SimpleGraph (Fin n)) (hG : DegreeBound d G)
    (U : Finset (Fin n)) (hU : 2 ≤ U.card) (hc : 0 < innerConductance d G U) :
    (∀ z ∈ coreComponent G U,
      elapsedMean (pathLaw (graphWalk d G) z) (firstVisit U 0) < ⊤) ∧
    ∀ x ∈ U, ∀ i : ℕ, 1 ≤ i →
      elapsedMean (pathLaw (graphWalk d G) x) (fun w => traceTime U w i) < ⊤ := by sorry

end InducedExpanderTest989.Structural
