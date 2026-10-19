-- Prove2me | Theorems.Thm_OAI_Brennan_isCompact_univalent_restrictions
-- name    : OAI.Brennan.isCompact_univalent_restrictions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T20:22:05.817477+00:00
-- url     : https://prove2.me/theorems/a3857553-297a-4582-ac41-b2562041938d
-- title:
--   Compactness of the class S of normalized univalent functions
-- statement:
--   Let $\mathbb D = \{z \in \mathbb C : |z| < 1\}$ (`Metric.ball (0 : ℂ) 1`), and give the space $C(\mathbb D, \mathbb C)$ of continuous functions on $\mathbb D$ Mathlib's compact-open topology (on $\mathbb D$, the topology of locally uniform convergence). Let $\mathcal S|_{\mathbb D}$ be the set of $g \in C(\mathbb D, \mathbb C)$ that are restrictions of normalized univalent functions: there is $f : \mathbb C \to \mathbb C$ such that
--   - $f$ is complex differentiable at every point of $\mathbb D$ (`DifferentiableOn ℂ f (Metric.ball 0 1)`);
--   - $f$ is injective on $\mathbb D$ (`Set.InjOn f (Metric.ball 0 1)`);
--   - $f(0) = 0$ and $f'(0) = 1$ ($f'$ is Mathlib's `deriv f`);
--   - $g(z) = f(z)$ for every $z \in \mathbb D$.
--
--   Then $\mathcal S|_{\mathbb D}$ is a compact subset of $C(\mathbb D, \mathbb C)$ (`IsCompact`).
--
--   This is the classical compactness of the class $\mathcal S$ of normalized univalent functions on the unit disk in the topology of locally uniform convergence. It is the form in which the class enters arguments that average over $\mathcal S$ or extract convergent subsequences.
--
--   Lean: `OAI.Brennan.isCompact_univalent_restrictions`. It restates OpenAI's lemma `OAI.Brennan.isCompact_diskSchlichtSet` (in `lean/OAI/Analysis/IntegralMeans/CompactClass.lean`), which is about OpenAI's set `diskSchlichtSet`, with the set described in Mathlib terms. The statement uses Mathlib alone and imports no definitions bundle.
-- source:
--   Classical theorem (compactness of the class S of normalized univalent functions). Lean proof: OpenAI, Brennan's conjecture and sharp inverse-square integral means, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 072; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brennans-conjecture-and-sharp-inverse-square-integral-means-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/IntegralMeans/CompactClass.lean (declaration OAI.Brennan.isCompact_diskSchlichtSet, restated with Mathlib-only definitions)

import Mathlib

theorem OAI.Brennan.isCompact_univalent_restrictions :
    IsCompact {g : C(Metric.ball (0 : ℂ) 1, ℂ) | ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f (Metric.ball 0 1) ∧ Set.InjOn f (Metric.ball 0 1) ∧
      f 0 = 0 ∧ deriv f 0 = 1 ∧ ∀ z : Metric.ball (0 : ℂ) 1, g z = f z} := by
  sorry
