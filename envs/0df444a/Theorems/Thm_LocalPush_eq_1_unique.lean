-- Prove2me | Theorems.Thm_LocalPush_eq_1_unique
-- name    : LocalPush.eq_1_unique
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:05:50.373928+00:00
-- url     : https://prove2.me/theorems/4ee07d70-944a-4ae1-a267-0a3b55b51ac9
-- title:
--   Eq. (1) — $\mathrm{pr}_\alpha(s)$ is the unique solution of the PageRank system
-- statement:
--   Let $G$ be a finite simple graph without isolated nodes and $\alpha\in(0,1)$. For every source vector $\sigma\in\mathbb R^V$, the vector $\mathrm{pr}_\alpha(\sigma)=\alpha(I-(1-\alpha)AD^{-1})^{-1}\sigma$ solves
--   $$p=\alpha\sigma+(1-\alpha)AD^{-1}p,\tag{1}$$
--   and every solution $p$ of (1) equals it.
--
--   This certifies that the matrix-inverse definition of PageRank used by the mission is the paper's definition.
--
--   Differences from the source:
--   - encoding: D⁻¹ → Dinv G, the diagonal matrix of reciprocal degrees; reason: every degree is positive (no isolated nodes), so it is the inverse of D
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §1.1, eq. (1), p.4 (PDF p.4)

import Mathlib
import Definitions.Def_LocalPush_PageRank

open Finset Matrix

namespace LocalPush

/-- **Eq. (1): `pr_α(s)` is the unique solution of the PageRank system.**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §1.1, eq. (1), p.4 (PDF p.4).

"For any source vector s ∈ ℝ^V and a teleportation parameter α ∈ (0, 1), we use pr_α(s) ∈ ℝ^V to denote its
PageRank vector, which is defined as the unique solution to the linear system pr_α(s) = αs + (1 − α)AD⁻¹pr_α(s)."

For a simple graph without isolated nodes and `α ∈ (0, 1)`, the vector `pr G α σ` solves (1), and every
solution of (1) equals it.

**Formalization Note.** `pr` is defined through the matrix inverse of `I − (1 − α)AD⁻¹`; this statement is what
certifies that the inverse is the paper's unique solution. `Dinv G` is the diagonal matrix of reciprocal
degrees, which is `D⁻¹` because every degree is positive. -/
theorem eq_1_unique {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (σ : V → ℝ) :
    pr G α σ = α • σ + (1 - α) • ((adjM G * Dinv G) *ᵥ pr G α σ) ∧
      ∀ p : V → ℝ, p = α • σ + (1 - α) • ((adjM G * Dinv G) *ᵥ p) → p = pr G α σ := by sorry

end LocalPush
