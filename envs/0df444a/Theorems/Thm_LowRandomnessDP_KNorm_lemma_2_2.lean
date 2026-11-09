-- Prove2me | Theorems.Thm_LowRandomnessDP_KNorm_lemma_2_2
-- name    : LowRandomnessDP.KNorm.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:10.192832+00:00
-- url     : https://prove2.me/theorems/147c4aea-e232-4219-87c1-0a7e571aedae
-- title:
--   Lemma 2.2 — two-norm volumetric net
-- statement:
--   Let $n_1,n_2$ be arbitrary norms on $\mathbb R^d$ with unit balls $B_1,B_2$ and $B_2\subseteq B_1$. For every $\delta>0$, there exists a finite $A\subseteq B_1$ such that every $x\in B_1$ has $y\in A$ with $n_2(x-y)\le\delta$, and
--
--   $$|A|\le(1+2/\delta)^d\frac{\operatorname{vol}(B_1)}{\operatorname{vol}(B_2)}.$$
--
--   Both unit-ball volumes are positive and finite. This supplies covering targets for the partition geometry.
--
--   Differences from the source:
--   - encoding: two arbitrary norms → positive-definite real seminorms on Fin d → ℝ; reason: Mathlib seminorms already encode triangle and absolute homogeneity; positive definiteness makes them exactly norms
--   - generalization: the net cardinal bound → the same net bound together with positivity and finiteness of both unit-ball volumes; reason: these are consequences of finite-dimensional norm unit balls and make the denominator safeguards explicit
-- source:
--   Surendra Ghentiyala, Pritish Kamath, Ravi Kumar, Pasin Manurangsi, STOC 2027 submission #514 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/514.pdf, Lemma 2.2, PDF page 7 / printed page 5

import Definitions.Def_LowRandomnessDP_KNorm_Sampling

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace LowRandomnessDP.KNorm

theorem lemma_2_2 (d : ℕ) (n₁ n₂ : Seminorm ℝ (Vec d))
    (h₁ : ∀ x, n₁ x = 0 → x = 0) (h₂ : ∀ x, n₂ x = 0 → x = 0)
    (hincl : {x | n₂ x ≤ 1} ⊆ {x | n₁ x ≤ 1})
    (δ : ℝ) (hδ : 0 < δ) :
    0 < volume {x | n₁ x ≤ 1} ∧ volume {x | n₁ x ≤ 1} < ⊤ ∧
    0 < volume {x | n₂ x ≤ 1} ∧ volume {x | n₂ x ≤ 1} < ⊤ ∧
    ∃ A : Finset (Vec d),
      (∀ y ∈ A, n₁ y ≤ 1) ∧
      (∀ x, n₁ x ≤ 1 → ∃ y ∈ A, n₂ (x - y) ≤ δ) ∧
      (A.card : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + 2 / δ) ^ d) *
        volume {x | n₁ x ≤ 1} / volume {x | n₂ x ≤ 1} := by sorry

end LowRandomnessDP.KNorm
