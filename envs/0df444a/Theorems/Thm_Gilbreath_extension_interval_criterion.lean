-- Prove2me | Theorems.Thm_Gilbreath_extension_interval_criterion
-- name    : Gilbreath.extension_interval_criterion
-- status  : Proved
-- author  : @EvanLLL
-- created : 2026-09-26T00:12:28.796529+00:00
-- url     : https://prove2.me/theorems/6f812e82-c14b-42f7-a45d-c6e2343b8458
-- title:
--   Ordered completeness criterion for binary-target folding
-- statement:
--   Let $E=(e_0,\ldots,e_{m-1})$ be an ordered tuple of nonnegative integers, and let $F_E(x)$ successively apply $x\mapsto|x-e_i|$ in the displayed order. Then
--   $$
--   \{x\in\mathbb N:F_E(x)\le1\}
--   =\{0,1,\ldots,1+\textstyle\sum_i e_i\}
--   $$
--   if and only if
--   $$
--   e_i\le1+\sum_{r>i}e_r\qquad(0\le i<m).
--   $$
--
--   The tuple's order is fixed; the inequalities do not permit sorting. The empty tuple is included. This characterizes when every input in the candidate interval produces a binary output, and supplies the deterministic interval criterion for extending the normalized prime-gap triangle.
-- source:
--   L. Muney, Holes in Valid-Extension Sets of Finite Gilbreath Sequences, arXiv:2606.23721v1, https://arxiv.org/html/2606.23721v1, Section 9, Theorem 20: the normalized reverse process starts from {0,1}, and the ordered preimage claim yields the displayed inequalities. This theorem formalizes that normalized core for an arbitrary ordered tuple and terminal target {0,1}.

import Definitions.Def_gilbreath_finite_extension

namespace Gilbreath
theorem extension_interval_criterion (es : List ℕ) :
    (∀ x : ℕ, extensionFold es x ≤ 1 ↔ x ≤ es.sum + 1) ↔
      ExtensionComplete es := by sorry
end Gilbreath
