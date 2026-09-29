-- Prove2me | Theorems.Thm_Gilbreath_chase_hunter_tao_parentage
-- name    : Gilbreath.chase_hunter_tao_parentage
-- status  : Proved
-- author  : @EvanLLL
-- created : 2026-09-24T23:39:45.648505+00:00
-- url     : https://prove2.me/theorems/20a8c401-0d9c-4833-9261-d76cdec63742
-- title:
--   Parentage trichotomy for a {0,d}-valued Gilbreath block
-- statement:
--   Let d be positive. Suppose a nonempty block of adjacent absolute differences of a nonnegative integer sequence takes values only in {0,d} and attains d. Then its parent block satisfies one of three alternatives: some entry is at least 2d; or every entry is 0 or d and both values occur; or there is 0<r<d such that every entry is r or r+d and both values occur. The Lean statement uses a zero-based block of k child entries and k+1 parent entries.
-- source:
--   Z. Chase, Z. Hunter, T. Tao, Gilbreath's conjecture: a Cramér random model and a deterministic analysis, arXiv:2607.08712v1, p. 14, Lemma 3.8 (Parentage), https://arxiv.org/pdf/2607.08712v1. This is the zero-based local-sequence form of the three alternatives.

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem chase_hunter_tao_parentage (a : ℕ → ℕ) (n k D : ℕ)
    (hD : 0 < D)
    (hchild : ∀ t, t < k →
      absDiff a (n + t) = 0 ∨ absDiff a (n + t) = D)
    (hatt : ∃ t, t < k ∧ absDiff a (n + t) = D) :
    (∃ u, u ≤ k ∧ 2 * D ≤ a (n + u)) ∨
    ((∀ t, t ≤ k → a (n + t) = 0 ∨ a (n + t) = D) ∧
      (∃ u, u ≤ k ∧ a (n + u) = 0) ∧
      (∃ v, v ≤ k ∧ a (n + v) = D)) ∨
    (∃ r, 0 < r ∧ r < D ∧
      (∀ t, t ≤ k → a (n + t) = r ∨ a (n + t) = r + D) ∧
      (∃ u, u ≤ k ∧ a (n + u) = r) ∧
      (∃ v, v ≤ k ∧ a (n + v) = r + D)) := by sorry
end Gilbreath
