-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_lemma_4_9
-- name    : InducedExpanderTest989.Structural.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:01:00.679217+00:00
-- url     : https://prove2.me/theorems/c1e2afa4-9d68-4dce-aea0-873c80d8fb70
-- title:
--   Lemma 4.9 — high-confidence intersection from shared mass
-- statement:
--   Let p,q be probability distributions on n vertices. Suppose Λ≥1 and 1≤ω≤n/Λ. Draw independent lists A,D of independent samples from p,q, respectively, with lengths m_A=⌈32√(nΛω)⌉ and m_D=⌈32√(nΛ/ω)⌉. Then
--   $$\|p-q\|_{\rm TV}\le1/4\ \Longrightarrow\ \Pr[A\cap D=\varnothing]\le e^{-\Lambda},\qquad
--   \Pr[A\cap D\ne\varnothing]\le1089n\Lambda\langle p,q\rangle.$$
--   Both the high-confidence guarantee and the arbitrary-distribution collision bound are retained. The experiment has deterministic list lengths and independent sampling, including between the two lists.
--
--   Differences from the source:
--   - encoding: independent lists sampled from probability distributions → probability vectors in stdSimplex and a finite sum of product weights; reason: this is exactly the independent product law, including repeated endpoints
--   - encoding: real parameters, natural logarithms and integer ceilings → Real.log, Real.sqrt, Nat.ceil and real powers; reason: all arguments have their stated positive domains; Nat.ceil agrees with the paper on those domains
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.25 (PDF p.27), Lemma 4.9; Definition 4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem lemma_4_9 {n : ℕ} (p q : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (hq : q ∈ stdSimplex ℝ (Fin n))
    (Λ ω : ℝ) (hΛ : 1 ≤ Λ) (hω : 1 ≤ ω ∧ ω ≤ n/Λ) :
    let a := ⌈32 * Real.sqrt (n*Λ*ω)⌉₊
    let b := ⌈32 * Real.sqrt (n*Λ/ω)⌉₊
    (MarkovChain.tvDist p q ≤ 1/4 → 1 - collisionProb p q a b ≤ Real.exp (-Λ)) ∧
    collisionProb p q a b ≤ 1089 * n * Λ * dot p q := by sorry

end InducedExpanderTest989.Structural
