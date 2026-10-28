-- Prove2me | Theorems.Thm_LipBernoulli_MultiUtility_lemma_3_1
-- name    : LipBernoulli.MultiUtility.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:22.172595+00:00
-- url     : https://prove2.me/theorems/88727049-f523-46c9-9a3b-4cbef1316dba
-- title:
--   Lemma 3.1, p. 9 — weakly affine preorders are preserved by mixing on either side and by mixing two comparisons
-- statement:
--   Let $X$ be a metric space with its Borel $\sigma$-algebra and let $\succsim$ be a weakly affine preorder on a nonempty convex set $S$ of Borel probability measures on $X$. Then for any $p, p', q, q', r \in S$ and any $\lambda \in [0,1]$:
--
--   1. $p \succsim q$ implies $r \oplus_\lambda p \succsim r \oplus_\lambda q$;
--   2. $p \succsim q$ and $p' \succsim q'$ imply $p \oplus_\lambda p' \succsim q \oplus_\lambda q'$.
--
--   Here $p \oplus_\lambda q = (1-\lambda)p + \lambda q$. The second part shows that the set $\{p - q : p \succsim q\}$ is convex, which is the convexity half of Lemma 4.5.
--
--   **Formalization Note** The weight $\lambda$ is named `t`. Note that weak affinity is required only for $\lambda \in [0,1)$ while the lemma's conclusion covers $\lambda\in[0,1]$.
-- source:
--   Ok & Weaver, Lipschitz Bernoulli Utility Functions, arXiv:2104.11205v1, Lemma 3.1, p. 9

import Mathlib
import Definitions.Def_LipBernoulli_MultiUtility_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace LipBernoulli.MultiUtility

/-- Lemma 3.1, p. 9. Let `≿` be a weakly affine preorder on a nonempty convex set `S` of Borel
probability measures on a metric space `X`. Then for any `p, p', q, q', r ∈ S` and `λ ∈ [0, 1]`:
`p ≿ q` implies `r ⊕_λ p ≿ r ⊕_λ q`, and `p ≿ q`, `p' ≿ q'` imply `p ⊕_λ p' ≿ q ⊕_λ q'`. -/
theorem lemma_3_1 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : Set (Measure X)) (hS : ∀ p ∈ S, IsProbabilityMeasure p) (hconv : IsConvexSet S)
    (hne : S.Nonempty) (R : Measure X → Measure X → Prop) (hpre : IsPreorderOn S R)
    (hwa : IsWeaklyAffine S R) :
    ∀ p ∈ S, ∀ p' ∈ S, ∀ q ∈ S, ∀ q' ∈ S, ∀ r ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (R p q → R (mix t r p) (mix t r q)) ∧
      (R p q → R p' q' → R (mix t p p') (mix t q q')) := by sorry

end LipBernoulli.MultiUtility
