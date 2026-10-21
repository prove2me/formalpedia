-- Prove2me | Theorems.Thm_LipBernoulli_MultiUtility_lemma_4_5
-- name    : LipBernoulli.MultiUtility.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:09.78288+00:00
-- url     : https://prove2.me/theorems/e95560ef-be1d-42ad-ab71-b692d79d75e1
-- title:
--   Lemma 4.5, p. 15 — for a Lipschitz affine preorder the cone C is closed and convex in KR(X), and p ≿ q iff p − q ∈ C
-- statement:
--   Let $X$ be a separable metric space with its Borel $\sigma$-algebra and let $\succsim$ be a Lipschitz affine preorder on $\Delta_1(X)$. Let
--   $$
--   C := \{\alpha(p-q) : \alpha \ge 0,\ p, q\in\Delta_1(X),\ p \succsim q\}.
--   $$
--   Then
--
--   1. $C \subseteq \mathrm{KR}(X)$;
--   2. $C$ is convex: $(1-t)a + tb \in C$ for $a, b \in C$ and $t \in [0,1]$;
--   3. $C$ is closed in $(\mathrm{KR}(X), \|\cdot\|_{\mathrm{KR}})$: every $\sigma \in \mathrm{KR}(X)\setminus C$ has a radius $r > 0$ with $\|\sigma - \mu\|_{\mathrm{KR}} \ge r$ for all $\mu\in C$;
--   4. (16) for all $p, q \in \Delta_1(X)$: $p \succsim q$ if and only if $p - q \in C$.
--
--   The lemma turns a Lipschitz affine preorder into a closed convex cone of $\mathrm{KR}(X)$, so that the preorder can be recovered by separating hyperplanes, i.e. by bounded linear functionals, which Theorem 2.3 identifies with Lipschitz functions.
--
--   **Formalization Note** Closedness is stated metrically, as the existence of a ball of positive radius around each point of $\mathrm{KR}(X)\setminus C$ disjoint from $C$ (the form proved on p. 15), without putting a topology on $\mathrm{KR}(X)$. $p - q$ is the signed measure `diff p q`.
-- source:
--   Ok & Weaver, Lipschitz Bernoulli Utility Functions, arXiv:2104.11205v1, Lemma 4.5 and (16), p. 15

import Mathlib
import Definitions.Def_LipBernoulli_MultiUtility_Setting
import Definitions.Def_LipBernoulli_MultiUtility_KR

open MeasureTheory
open scoped ENNReal NNReal

namespace LipBernoulli.MultiUtility

/-- Lemma 4.5, p. 15. Let `X` be a separable metric space and `≿` a Lipschitz affine preorder on
`Δ₁(X)`. Then `C := {α(p − q) : α ≥ 0 and p ≿ q}` is a closed and convex subset of `KR(X)`, and
(16) `p ≿ q` iff `p − q ∈ C` for any `p, q ∈ Δ₁(X)`. Closedness is stated metrically: every
`σ ∈ KR(X) \ C` has a `‖·‖_KR`-ball of positive radius disjoint from `C`. -/
theorem lemma_4_5 {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (R : Measure X → Measure X → Prop) (hpre : IsPreorderOn (Delta1 X) R)
    (hlip : IsLipschitzPref R) (haff : IsAffine (Delta1 X) R) :
    coneC R ⊆ KR X ∧
    (∀ a ∈ coneC R, ∀ b ∈ coneC R, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) • a + t • b ∈ coneC R) ∧
    (∀ σ ∈ KR X, σ ∉ coneC R →
      ∃ r : ℝ, 0 < r ∧ ∀ μ ∈ coneC R, ENNReal.ofReal r ≤ krNorm (σ - μ)) ∧
    (∀ p ∈ Delta1 X, ∀ q ∈ Delta1 X, (R p q ↔ diff p q ∈ coneC R)) := by sorry

end LipBernoulli.MultiUtility
