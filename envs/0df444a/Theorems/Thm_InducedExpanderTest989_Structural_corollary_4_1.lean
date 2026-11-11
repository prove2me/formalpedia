-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_corollary_4_1
-- name    : InducedExpanderTest989.Structural.corollary_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:18.993862+00:00
-- url     : https://prove2.me/theorems/aeb4c500-42c9-43ed-9d16-29bc3a52335f
-- title:
--   Corollary 4.1 — average cross-part overlap
-- statement:
--   Suppose G has degree bound d≥1 on n>0 vertices, 0<α₀,ψ<1, and G∉P_{α₀,ψ}. There is a partition satisfying both conclusions of Lemma 4.7 for which, for every integer ℓ≥1,
--   $$\mathbb E_{x,y\sim\operatorname{Unif}(V)}[\mathbf1_{C(x)\ne C(y)}\langle e_xQ_\ell,e_yQ_\ell\rangle]<\ell\psi L/n,$$
--   where x,y are independent, Q_ℓ is the lazy averaging kernel and L=⌊log₂(1/α₀)⌋+1. The partition is chosen from the graph, independently of the averaging length; it is not an unrelated supplied object.
--
--   Differences from the source:
--   - encoding: vertices [n], slots [d], null symbol ⊥ → Fin n, zero-based Fin d slots, none; reason: renumbering preserves every adjacency list and graph
--   - encoding: a graph on a positive number of vertices → 0 < n is explicit; reason: uniform vertex sampling requires a nonempty vertex set, as in the standing query model
--   - encoding: partition into parts C₁,…,Cₛ → a finite vertex-label map C with its fibers as parts; reason: empty unused fibers may be deleted; crossing undirected edges are counted once by the smaller vertex label
--   - encoding: real parameters, natural logarithms and integer ceilings → Real.log, Real.sqrt, Nat.ceil and real powers; reason: all arguments have their stated positive domains; Nat.ceil agrees with the paper on those domains
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.24 (PDF p.26), Corollary 4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem corollary_4_1 {n d : ℕ} (hn : 0 < n) (hd : 1 ≤ d)
    (G : SimpleGraph (Fin n)) (hG : DegreeBound d G)
    (α₀ ψ : ℝ) (ha : 0 < α₀ ∧ α₀ < 1) (hψ : 0 < ψ ∧ ψ < 1)
    (hno : ¬ HasCore d G α₀ ψ) :
    ∃ (s : ℕ) (C : Fin n → Fin s),
      (∀ i, ((part C i).card : ℝ) < α₀*n) ∧
      (crossEdges G C : ℝ) < ψ*d*n*partitionLevels α₀ ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → crossOverlap (averaging (graphWalk d G) ℓ) C <
        ℓ * ψ * partitionLevels α₀ / n := by sorry

end InducedExpanderTest989.Structural
