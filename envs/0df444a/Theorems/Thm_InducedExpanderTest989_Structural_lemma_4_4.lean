-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_lemma_4_4
-- name    : InducedExpanderTest989.Structural.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:10.887142+00:00
-- url     : https://prove2.me/theorems/60df51c0-b0eb-4ed9-94df-90c1c29a878d
-- title:
--   Lemma 4.4 — Kac formula and trace cost
-- statement:
--   Let G have maximum degree at most d≥1. Let U contain at least two vertices and have positive inner conductance, and let C_U be its connected component. Write P for the lazy graph walk, P^U for its trace matrix on U, π_U for the uniform law on U, and τ_i for the time of its ith trace visit with τ₀=0.
--   Let c(x)=E_x[τ₁]. Then
--   $$\sum_{x\in U}c(x)=|C_U|,\qquad
--   \sum_{x\in U}(\mathbb E_x[\tau_t]-t)=t(|C_U|-|U|)\quad(t\ge1).$$
--   The real expectations are the conversions of the nonnegative extended integrals; Lemma 4.2 guarantees finiteness under these same hypotheses. Both identities are part of the statement.
--
--   Differences from the source:
--   - encoding: vertices [n], slots [d], null symbol ⊥ → Fin n, zero-based Fin d slots, none; reason: renumbering preserves every adjacency list and graph
--   - encoding: walk trajectories, infinite hitting times and expectations → Ionescu–Tulcea path measure, ℕ∞ visit times and extended nonnegative expectations; reason: never-hit paths retain infinity; real expectations are used only where Lemma 4.2 guarantees finiteness
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.18 (PDF p.20), Lemma 4.4; §4.2.1 standing preamble p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem lemma_4_4 {n d : ℕ} (hd : 1 ≤ d) (G : SimpleGraph (Fin n)) (hG : DegreeBound d G)
    (U : Finset (Fin n)) (hU : 2 ≤ U.card) (hc : 0 < innerConductance d G U) :
    (∑ x ∈ U, (elapsedMean (pathLaw (graphWalk d G) x)
      (fun w => traceTime U w 1)).toReal) = (coreComponent G U).card ∧
    ∀ t : ℕ, 1 ≤ t →
      (∑ x ∈ U, ((elapsedMean (pathLaw (graphWalk d G) x)
        (fun w => traceTime U w t)).toReal - t)) =
      (t : ℝ) * ((coreComponent G U).card - (U.card : ℝ)) := by sorry

end InducedExpanderTest989.Structural
