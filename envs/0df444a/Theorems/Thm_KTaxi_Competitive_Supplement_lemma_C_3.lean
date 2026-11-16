-- Prove2me | Theorems.Thm_KTaxi_Competitive_Supplement_lemma_C_3
-- name    : KTaxi.Competitive.Supplement.lemma_C_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:33:04.646134+00:00
-- url     : https://prove2.me/theorems/07ac0212-d18b-4108-8b6b-a0f3215b9194
-- title:
--   Lemma C.3 — incompatibility without regularity assumptions
-- statement:
--   For any finite $\rho\ge1$, no finite nonnegative function $F:\mathbb R^2\to[0,\infty)$ can satisfy all of the following constraints. For every $x,y$,
--   $$|x-y|\le F(x,y)\le\rho|x-y|,$$
--   and for every pairwise distinct $x,y,z$ there must be one $p\in[0,1]$ satisfying both
--   $$F(x,y)\ge p|x-y|+(1-p)(|z-y|+F(x,z)),$$
--   $$F(z,y)\ge(1-p)|z-y|+p(|x-y|+F(z,x)).$$
--   There is no symmetry, continuity, measurability or algorithm-realizability hypothesis. This independent incompatibility result supplies the final contradiction for Theorem 1.3.
--
--   Differences from the source:
--   - encoding: a finite nonnegative function on ℝ² and finite ρ ≥ 1 → a curried function ℝ → ℝ → ℝ≥0 and ρ : ℝ≥0 with 1 ≤ ρ; reason: currying and the nonnegative real type change no instance; both bounds and both comparisons are expanded in the theorem
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, STOC 2027 submission #96 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Lemma C.3, PDF p. 24 (printed p. 23)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Supplement_Memoryless

open scoped ENNReal NNReal

namespace KTaxi.Competitive.Supplement

/-- Lemma C.3, PDF p. 24: arbitrary finite nonnegative oriented functions,
without regularity or algorithm-realizability assumptions. -/
theorem lemma_C_3 (ρ : ℝ≥0) (hρ : 1 ≤ ρ) :
    ¬ ∃ F : ℝ → ℝ → ℝ≥0,
      (∀ x y : ℝ, |x - y| ≤ (F x y : ℝ) ∧
        (F x y : ℝ) ≤ (ρ : ℝ) * |x - y|) ∧
      (∀ x y z : ℝ, x ≠ y → x ≠ z → y ≠ z → ∃ p : ℝ,
        0 ≤ p ∧ p ≤ 1 ∧
        p * |x - y| + (1 - p) * (|z - y| + (F x z : ℝ)) ≤ (F x y : ℝ) ∧
        (1 - p) * |z - y| + p * (|x - y| + (F z x : ℝ)) ≤ (F z y : ℝ)) := by sorry

end KTaxi.Competitive.Supplement
