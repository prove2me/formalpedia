-- Prove2me | Theorems.Thm_MetricTesting_Characterization_Supplement_injective_geometric_completion_obstructions
-- name    : MetricTesting.Characterization.Supplement.injective_geometric_completion_obstructions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:26:01.982225+00:00
-- url     : https://prove2.me/theorems/35ff2d31-88f0-4049-a948-9a19a77c3de4
-- title:
--   Theorem 5.20 — Injective tree and Euclidean completion obstructions
-- statement:
--   For strict tree metrics, and for strict Euclidean metrics in every fixed integer dimension $d\ge1$, both on nonnegative ambient inputs and on positive ambient inputs, the local predicates admit completion obstructions and are not removable. In each case,
--
--   $$\exists\gamma>0,\ s_j\to\infty,\ A^{(j)}\text{ locally consistent}:\quad
--   \frac{|H(A^{(j)})|}{s_j^2}\to0,\qquad\operatorname{cdist}(A^{(j)})\ge\gamma.$$
--
--   Neither strict family has a constant-query one-sided tester. Strict means positive off-diagonal distances, hence injective geometric realizations at and above the predicate arity. Trees may have labeled internal vertices and additional unlabeled vertices; Euclidean distances are ordinary distances in $\mathbb R^d$.
--
--   This identifies the completion obstruction created by injectivity. The local-family convention below arity is retained, and the sequence orders are all at least the arity.
--
--   Differences from the source:
--   - encoding: symmetric zero-diagonal arrays on [n] and local validity → the published unordered-pair Array on Fin n, with inherited local-family conventions; reason: relabeling preserves every input, target, discrepancy and query
--   - encoding: strict tree and Euclidean completion obstructions → explicit completion-obstruction sequences for both ambient domains, using four-point and exact Euclidean local predicates; reason: the source gives the equivalent four-point tree characterization; strict positivity supplies injectivity and small orders retain local vacuity
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 25, Theorem 5.20 (PDF p. 26); SHA-256 3e49396763fea65b4a7151b904f1cba07f70024d5c851dce84339c98c8148be9

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_completion
import Definitions.Def_MetricTesting_Characterization_decision_tree

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

theorem injective_geometric_completion_obstructions :
    (∀ ambient : Bool, CompletionObstruction (strictTree ambient) ∧
      ¬ Removable (strictTree ambient) ∧ ¬ OneSidedTestable (strictTree ambient)) ∧
    (∀ d : ℕ, 1 ≤ d → ∀ ambient : Bool,
      CompletionObstruction (strictEuclidean d ambient) ∧
      ¬ Removable (strictEuclidean d ambient) ∧
      ¬ OneSidedTestable (strictEuclidean d ambient)) := by sorry

end MetricTesting.Characterization.Supplement
