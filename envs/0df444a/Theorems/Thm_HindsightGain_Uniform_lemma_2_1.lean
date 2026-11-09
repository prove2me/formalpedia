-- Prove2me | Theorems.Thm_HindsightGain_Uniform_lemma_2_1
-- name    : HindsightGain.Uniform.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:32.583602+00:00
-- url     : https://prove2.me/theorems/b7f87f7f-c48b-4fc5-a895-9e4dbc9d7240
-- title:
--   Lemma 2.1 — Exact convexification
-- statement:
--   Fix integers $n,D\ge1$, $r\ge2$ and a model of arbitrary nonempty compact local domains $K_i$ in Euclidean unit balls with multilinear interactions $A_e$. For every nonnegative weight vector $a$, let $Z_a=\prod_i a_i\operatorname{conv}K_i$ and $f_A=f_{A,\mathbf1}$. Then
--   $$\operatorname{Val}_A(a)=\max_{y\in Z_a}f_A(y).$$
--   The maximum on the right is attained. This identifies the original weighted optimum with a fixed objective on a scaled convex body without imposing convexity on the local domains.
--
--   Differences from the source:
--   - encoding: arbitrary multilinear interactions on r-element subsets of [n] and Euclidean local domains → coefficient arrays on cardinality-r Finsets of Fin n, with each interaction evaluated in increasing order in EuclideanSpace ℝ (Fin D); reason: orthonormal coordinates encode every source multilinear map uniquely, preserving its coefficient Frobenius norm and every compact local domain
--   - encoding: a maximum over the compact product domain → the real sSup of the actual polynomial image; reason: Model includes all source nonemptiness and compactness assumptions, so the image is nonempty, compact, bounded and has an attained maximum
--   - encoding: max over Z_a → a real supremum together with an attaining point in Z_a; reason: this spells out the attainment in the source maximum rather than assuming it
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Lemma 2.1, (10), p.13

import Mathlib
import Definitions.Def_HindsightGain_Uniform_optima

set_option autoImplicit false

namespace HindsightGain.Uniform

/-- Lemma 2.1 (10), p.13: the real maximum on Z_a, including its attainment. -/
theorem lemma_2_1 {n D r : ℕ} (M : Model n D r) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    val M a = sSup (objective M (fun _ => 1) '' convexBody M a) ∧
      ∃ y ∈ convexBody M a, objective M (fun _ => 1) y = val M a := by sorry

end HindsightGain.Uniform
