-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_lemma_3_3
-- name    : InducedExpanderTest989.Structural.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:05.36052+00:00
-- url     : https://prove2.me/theorems/0f15626b-1022-43cc-9f6a-ba1b9d88ca57
-- title:
--   Lemma 3.3 — Cheeger energy and lazy mixing bounds
-- statement:
--   Let K be a symmetric stochastic matrix on a finite nonempty state space Ω, and π the uniform law. Suppose 0<h≤1 and Φ(K)≥h. Every real function f of π-mean zero satisfies
--   $$\mathcal E_K(f)\ge\frac{h^2}{2}\|f\|_{2,\pi}^2.$$
--   If also K(x,x)≥1/2 for every x, then for every state x and integer t≥0,
--   $$\|e_xK^t-\pi\|_{\rm TV}\le\tfrac12\sqrt{|\Omega|}\exp(-h^2t/2).$$
--   Both conclusions are retained, without an irreducibility assumption. On a singleton they are trivial; chain conductance there is defined as 1.
--
--   Differences from the source:
--   - encoding: finite stochastic matrix and row-vector total variation → Mathlib rowStochastic, Matrix powers and MarkovChain.tvDist; reason: the existing finite-chain definitions use the same row convention and add no irreducibility assumption
--   - encoding: uniform distribution on a finite state space → Nonempty is explicit and the empty cut family has conductance 1; reason: a uniform probability law needs a state; this convention also covers the singleton case
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.14 (PDF p.16), Lemma 3.3; Appendix A.1 pp.50–51; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem lemma_3_3 {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (K : Matrix X X ℝ) (hK : Stochastic K) (hs : K.IsSymm)
    (h : ℝ) (hh : 0 < h ∧ h ≤ 1) (hc : h ≤ chainConductance K) :
    (∀ f : X → ℝ, (∑ x, MarkovChain.unif X x * f x) = 0 →
      h^2 / 2 * weightedSq f ≤ energy K f) ∧
    ((∀ x, (1:ℝ)/2 ≤ K x x) → ∀ (x : X) (t : ℕ),
      MarkovChain.tvDist ((K^t) x) (MarkovChain.unif X) ≤
        (1:ℝ)/2 * Real.sqrt (Fintype.card X) * Real.exp (-h^2 * t / 2)) := by sorry

end InducedExpanderTest989.Structural
