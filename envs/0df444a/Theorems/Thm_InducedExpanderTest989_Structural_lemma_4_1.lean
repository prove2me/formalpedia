-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_lemma_4_1
-- name    : InducedExpanderTest989.Structural.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:03.423314+00:00
-- url     : https://prove2.me/theorems/e7373449-5c44-4f45-9f9f-970c9b2ce623
-- title:
--   Lemma 4.1 — symmetry and laziness
-- statement:
--   Let G have maximum degree at most d≥1. Let U contain at least two vertices and have positive inner conductance, and let C_U be its connected component. Write P for the lazy graph walk, P^U for its trace matrix on U, π_U for the uniform law on U, and τ_i for the time of its ith trace visit with τ₀=0.
--   Then P^U is symmetric and stochastic, π_U is stationary, and
--   $$P^U(x,x)\ge1/2\quad(x\in U).$$
--   These are all the source conclusions; the core's exterior remains arbitrary.
--
--   Differences from the source:
--   - encoding: vertices [n], slots [d], null symbol ⊥ → Fin n, zero-based Fin d slots, none; reason: renumbering preserves every adjacency list and graph
--   - encoding: walk trajectories, infinite hitting times and expectations → Ionescu–Tulcea path measure, ℕ∞ visit times and extended nonnegative expectations; reason: never-hit paths retain infinity; real expectations are used only where Lemma 4.2 guarantees finiteness
--   - encoding: finite stochastic matrix and row-vector total variation → Mathlib rowStochastic, Matrix powers and MarkovChain.tvDist; reason: the existing finite-chain definitions use the same row convention and add no irreducibility assumption
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.16 (PDF p.18), Lemma 4.1; §4.2.1 standing preamble; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem lemma_4_1 {n d : ℕ} (hd : 1 ≤ d) (G : SimpleGraph (Fin n)) (hG : DegreeBound d G)
    (U : Finset (Fin n)) (hU : 2 ≤ U.card) (hc : 0 < innerConductance d G U) :
    (traceMatrix d G U).IsSymm ∧ Stochastic (traceMatrix d G U) ∧
    Matrix.vecMul (MarkovChain.unif U) (traceMatrix d G U) = MarkovChain.unif U ∧
    ∀ x : U, (1:ℝ)/2 ≤ traceMatrix d G U x x := by sorry

end InducedExpanderTest989.Structural
