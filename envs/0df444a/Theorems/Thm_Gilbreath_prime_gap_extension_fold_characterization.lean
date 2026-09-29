-- Prove2me | Theorems.Thm_Gilbreath_prime_gap_extension_fold_characterization
-- name    : Gilbreath.prime_gap_extension_fold_characterization
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T00:56:02.690376+00:00
-- url     : https://prove2.me/theorems/a7976cb5-5282-40f1-b493-8359ca3e905f
-- title:
--   Folding-interval characterization for prime-gap boundaries
-- statement:
--   Let $b : \mathbb{N} \to \mathbb{N}$ satisfy $d^1(n+1) = 2b_n$ for all $n$, where $d^1$ is the prime-gap row of the Gilbreath triangle, and let $E_n$ be the ordered right boundary of its first $n$ entries. Assume the leading entries below $n$ are binary, $(\Delta^j b)(0) \le 1$ for $j < n$. Then folding is an exact interval test on $E_n$:
--
--   $$
--   F_{E_n}(x) \le 1 \quad\Longleftrightarrow\quad x \le 1 + \sum_{e \in E_n} e \qquad (x \in \mathbb{N}).
--   $$
--
--   This is the folding-language form of ordered boundary completeness for prime-gap prefixes: by the proved interval criterion it is equivalent to the completeness assertion, while its left-to-right reading is what the finite-extension induction step consumes (via the boundary-bottom identity, the next gap folds to the next triangle bottom). Like its parent, this is a new prime-specific conjecture for the decomposition, not a claim made in the cited paper.
--
--   **Formalization Note** Uses the folding map and boundary from the finite-extension definitions with terminal target $\{0, 1\}$.
-- source:
--   Folding-language form of Gilbreath.prime_gap_ordered_extension_condition, formulated for Prove2Me decomposition; equivalent to it via the proved Gilbreath.extension_interval_criterion. General folding background: L. Muney, Holes in Valid-Extension Sets of Finite Gilbreath Sequences, arXiv:2606.23721v1, Sections 2, 8, 9 (Theorem 20), https://arxiv.org/html/2606.23721v1. The prime-specific assertion is a new open conjecture, not a result of that paper.

import Definitions.Def_gilbreath_finite_extension

namespace Gilbreath
theorem prime_gap_extension_fold_characterization (b : ℕ → ℕ)
    (hb : ∀ n, d 1 (n + 1) = 2 * b n) (n : ℕ)
    (hprefix : ∀ j, j < n → iterAbsDiff b j 0 ≤ 1) :
    ∀ x : ℕ, extensionFold (extensionBoundary b n) x ≤ 1 ↔
      x ≤ (extensionBoundary b n).sum + 1 := by sorry
end Gilbreath
