-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_lemma_3_1
-- name    : InducedExpanderTest989.Structural.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:30.669278+00:00
-- url     : https://prove2.me/theorems/c272b943-14f4-49fc-8258-5b86033f9c62
-- title:
--   Lemma 3.1 — monotonicity
-- statement:
--   Let G have degree bound d≥1 and let α,α′,ϕ,ϕ′ lie in (0,1]. If α′≤α and ϕ′≤ϕ, then
--   $$G\in P_{\alpha,\phi}\ \Longrightarrow\ G\in P_{\alpha',\phi'}.$$
--   This permits relaxing either core threshold and gives the reduction for κ<3/4.
--
--   Differences from the source:
--   - encoding: vertices [n], slots [d], null symbol ⊥ → Fin n, zero-based Fin d slots, none; reason: renumbering preserves every adjacency list and graph
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.13 (PDF p.15), Lemma 3.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem lemma_3_1 {n d : ℕ} (hd : 1 ≤ d) (G : SimpleGraph (Fin n))
    (hG : DegreeBound d G) (α α' ϕ ϕ' : ℝ)
    (hα : 0 < α ∧ α ≤ 1) (hα' : 0 < α' ∧ α' ≤ 1)
    (hϕ : 0 < ϕ ∧ ϕ ≤ 1) (hϕ' : 0 < ϕ' ∧ ϕ' ≤ 1)
    (ha : α' ≤ α) (hf : ϕ' ≤ ϕ) : HasCore d G α ϕ → HasCore d G α' ϕ'  := by sorry

end InducedExpanderTest989.Structural
