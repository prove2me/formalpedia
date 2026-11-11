-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_lemma_4_8
-- name    : InducedExpanderTest989.Structural.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:27.815721+00:00
-- url     : https://prove2.me/theorems/612542ce-9dae-4d5a-9948-8efe0918cdd4
-- title:
--   Lemma 4.8 — overlap is bounded by cross flow
-- statement:
--   Let Q be a symmetric stochastic matrix on n vertices, q_x its row, and Q(S,T)=∑_{x∈S,y∈T}Q(x,y). For every vertex set A,
--   $$\sum_{x\in A,y\notin A}\langle q_x,q_y\rangle\le2Q(A,V\setminus A).$$
--   Also let G have degree bound d≥1, C any partition and F its crossing edges. For every ℓ≥1 and the lazy averaging kernel Q_ℓ of G,
--   $$\frac1{n^2}\sum_{C(x)\ne C(y)}\langle e_xQ_\ell,e_yQ_\ell\rangle\le\frac{\ell|F|}{dn^2}.$$
--   Both sums use ordered pairs. The first clause is for arbitrary Q; the second is for the graph walk and does not identify Q with Q_ℓ.
--
--   Differences from the source:
--   - encoding: vertices [n], slots [d], null symbol ⊥ → Fin n, zero-based Fin d slots, none; reason: renumbering preserves every adjacency list and graph
--   - encoding: a graph on a positive number of vertices → 0 < n is explicit; reason: uniform vertex sampling requires a nonempty vertex set, as in the standing query model
--   - encoding: partition into parts C₁,…,Cₛ → a finite vertex-label map C with its fibers as parts; reason: empty unused fibers may be deleted; crossing undirected edges are counted once by the smaller vertex label
--   - encoding: finite stochastic matrix and row-vector total variation → Mathlib rowStochastic, Matrix powers and MarkovChain.tvDist; reason: the existing finite-chain definitions use the same row convention and add no irreducibility assumption
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.23 (PDF p.25), Lemma 4.8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem lemma_4_8 {n d : ℕ} (hn : 0 < n) (hd : 1 ≤ d)
    (G : SimpleGraph (Fin n)) (hG : DegreeBound d G)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Stochastic Q) (hs : Q.IsSymm) :
    (∀ A : Finset (Fin n),
      (∑ x ∈ A, ∑ y ∈ Aᶜ, dot (Q x) (Q y)) ≤ 2 * (∑ x ∈ A, ∑ y ∈ Aᶜ, Q x y)) ∧
    ∀ (s : ℕ) (C : Fin n → Fin s) (ℓ : ℕ), 1 ≤ ℓ →
      crossOverlap (averaging (graphWalk d G) ℓ) C ≤
        ℓ * (crossEdges G C : ℝ) / (d * (n : ℝ)^2) := by sorry

end InducedExpanderTest989.Structural
