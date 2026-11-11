-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_lemma_4_11
-- name    : InducedExpanderTest989.Structural.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:38.802768+00:00
-- url     : https://prove2.me/theorems/375401f2-cc30-433a-9698-03e1cc0758fd
-- title:
--   Lemma 4.11 — estimating a conditional score
-- statement:
--   Let 0<α≤1 and 3/4≤κ<1, β=(1−κ)α, and k=⌈64αβ⁻²log(128/α)⌉. For any score s∈[0,1], let N have binomial law Bin(k,s) and call the anchor flagged when N/k≥α−β/2. Then
--   $$s\ge\alpha-\beta/4\ \Longrightarrow\ \Pr[\mathrm{flag}]\ge1-\alpha/64,\qquad
--   s\le\alpha-3\beta/4\ \Longrightarrow\ \Pr[\mathrm{flag}]\le\alpha/64.$$
--   Taking s=f(x,A) recovers the paper's conditional anchor-state claim.
--
--   Differences from the source:
--   - generalization: s is the conditional score f(x,A) of a fixed anchor state → any real s in [0,1] with N distributed as Bin(k,s); reason: the conditional partner count has this binomial law, so substitution recovers every source instance
--   - encoding: a binomial event probability → the finite sum of binomial masses over the threshold event; reason: this preserves the full distribution and both inclusive flag thresholds
--   - encoding: real parameters, natural logarithms and integer ceilings → Real.log, Real.sqrt, Nat.ceil and real powers; reason: all arguments have their stated positive domains; Nat.ceil agrees with the paper on those domains
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.30 (PDF p.32), Lemma 4.11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem lemma_4_11 (α κ score : ℝ) (hα : 0 < α ∧ α ≤ 1)
    (hκ : 3/4 ≤ κ ∧ κ < 1) (hs : 0 ≤ score ∧ score ≤ 1) :
    let flag := binomialEvent (partners α κ) score
      (fun j => α-beta α κ/2 ≤ (j : ℝ)/partners α κ)
    (α-beta α κ/4 ≤ score → 1-α/64 ≤ flag) ∧
    (score ≤ α-3*beta α κ/4 → flag ≤ α/64) := by sorry

end InducedExpanderTest989.Structural
