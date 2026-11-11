-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_lemma_4_7
-- name    : InducedExpanderTest989.Structural.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:31.81439+00:00
-- url     : https://prove2.me/theorems/a31025d4-f618-402c-a954-5f756a1ca01d
-- title:
--   Lemma 4.7 — sparse-cut partition
-- statement:
--   Let G be a graph on n>0 vertices of maximum degree at most d≥1. Let 0<α₀,ψ<1 and suppose G∉P_{α₀,ψ}. There is a partition into parts C_i, with F the edges joining different parts, such that
--   $$|C_i|<\alpha_0 n\quad\text{for every }i,\qquad |F|<\psi dnL,\qquad L=\lfloor\log_2(1/\alpha_0)\rfloor+1.$$
--   The parts are not assumed to expand. Both their size and the strict crossing-edge bound are asserted.
--
--   Differences from the source:
--   - encoding: vertices [n], slots [d], null symbol ⊥ → Fin n, zero-based Fin d slots, none; reason: renumbering preserves every adjacency list and graph
--   - encoding: a graph on a positive number of vertices → 0 < n is explicit; reason: uniform vertex sampling requires a nonempty vertex set, as in the standing query model
--   - encoding: partition into parts C₁,…,Cₛ → a finite vertex-label map C with its fibers as parts; reason: empty unused fibers may be deleted; crossing undirected edges are counted once by the smaller vertex label
--   - encoding: real parameters, natural logarithms and integer ceilings → Real.log, Real.sqrt, Nat.ceil and real powers; reason: all arguments have their stated positive domains; Nat.ceil agrees with the paper on those domains
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.22 (PDF p.24), Lemma 4.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem lemma_4_7 {n d : ℕ} (hn : 0 < n) (hd : 1 ≤ d)
    (G : SimpleGraph (Fin n)) (hG : DegreeBound d G)
    (α₀ ψ : ℝ) (ha : 0 < α₀ ∧ α₀ < 1) (hψ : 0 < ψ ∧ ψ < 1)
    (hno : ¬ HasCore d G α₀ ψ) :
    ∃ (s : ℕ) (C : Fin n → Fin s),
      (∀ i, ((part C i).card : ℝ) < α₀*n) ∧
      (crossEdges G C : ℝ) < ψ * d * n * partitionLevels α₀ := by sorry

end InducedExpanderTest989.Structural
