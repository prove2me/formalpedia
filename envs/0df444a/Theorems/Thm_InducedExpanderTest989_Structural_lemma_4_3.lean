-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_lemma_4_3
-- name    : InducedExpanderTest989.Structural.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:21.16147+00:00
-- url     : https://prove2.me/theorems/f6ccf49c-b03a-4db5-8bab-01d09131c1ee
-- title:
--   Lemma 4.3 — inherited conductance and mixing
-- statement:
--   Let G have maximum degree at most d≥1. Let U contain at least two vertices and have positive inner conductance, and let C_U be its connected component. Write P for the lazy graph walk, P^U for its trace matrix on U, π_U for the uniform law on U, and τ_i for the time of its ith trace visit with τ₀=0.
--   For ϕ∈(0,1], if Φ_in(G[U])≥ϕ, then
--   $$\Phi(P^U)\ge\phi/2,\qquad
--   \|e_x(P^U)^t-\pi_U\|_{\rm TV}\le\tfrac12\sqrt{|U|}\exp(-\phi^2t/8)\quad(x\in U,\ t\ge0).$$
--   The conductance factor is ϕ/2, as shown on the rendered page. Both bounds concern the trace chain, not global mixing.
--
--   Differences from the source:
--   - encoding: vertices [n], slots [d], null symbol ⊥ → Fin n, zero-based Fin d slots, none; reason: renumbering preserves every adjacency list and graph
--   - encoding: walk trajectories, infinite hitting times and expectations → Ionescu–Tulcea path measure, ℕ∞ visit times and extended nonnegative expectations; reason: never-hit paths retain infinity; real expectations are used only where Lemma 4.2 guarantees finiteness
--   - encoding: finite stochastic matrix and row-vector total variation → Mathlib rowStochastic, Matrix powers and MarkovChain.tvDist; reason: the existing finite-chain definitions use the same row convention and add no irreducibility assumption
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.18 (PDF p.20), Lemma 4.3; §4.2.1 standing preamble p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem lemma_4_3 {n d : ℕ} (hd : 1 ≤ d) (G : SimpleGraph (Fin n)) (hG : DegreeBound d G)
    (U : Finset (Fin n)) (hU : 2 ≤ U.card) (hc : 0 < innerConductance d G U) (ϕ : ℝ) (hϕ : 0 < ϕ ∧ ϕ ≤ 1)
    (he : ϕ ≤ innerConductance d G U) :
    ϕ/2 ≤ chainConductance (traceMatrix d G U) ∧
    ∀ (x : U) (t : ℕ),
      MarkovChain.tvDist ((traceMatrix d G U ^ t) x) (MarkovChain.unif U) ≤
        (1:ℝ)/2 * Real.sqrt U.card * Real.exp (-ϕ^2 * t / 8) := by sorry

end InducedExpanderTest989.Structural
