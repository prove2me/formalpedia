-- Prove2me | Theorems.Thm_LowRankIndicator_equation_4
-- name    : LowRankIndicator.equation_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:45.049295+00:00
-- url     : https://prove2.me/theorems/9959cee7-8393-4650-a3d6-34c870a284be
-- title:
--   Equation (4) — $V(I)\subseteq Q$ for every $I$, and $Q=\bigcup_{I\subseteq[n]}V(I)$
-- statement:
--   Let $f(x)=g(Ax)+c^\top x$, and let $Q$ and $V(I)$ be the sets of (2) and (3). For every $I\subseteq[n]$ one has $V(I)\subseteq Q$, and
--
--   $$Q=\bigcup_{I\subseteq[n]}V(I).$$
--
--   This is the disjunctive description of $Q$ by its $2^n$ support patterns, the starting point of the convexification.
--
--   Differences from the source:
--   - generalization: g proper closed convex → arbitrary g : ℝᵏ → `EReal`; reason: the statement holds without these properties and specializes to the paper's g, with +∞ as `⊤`
--   - encoding: I ⊆ [n], z ∈ {0,1}ⁿ, [n] = {1,…,n} → `Finset (Fin n)`, `∀ i, z i = 0 ∨ z i = 1`, 0-based `Fin n`; reason: Lean conventions, same instances
-- source:
--   Han & Gómez, Compact Extended Formulations for Low-Rank Functions with Indicator Variables, arXiv:2110.14884v2, equation (4), p.5.

import Mathlib
import Definitions.Def_LowRankIndicator_Sets

namespace LowRankIndicator

/-- **Equation (4)**, Han & Gómez, arXiv:2110.14884v2, p.5: "V(I) ⊆ Q" for every `I`, and
`Q = ⋃_{I⊆[n]} V(I)`.

**Formalization Note.** `g` is an arbitrary `EReal`-valued function: neither properness, closedness
nor convexity is used. The union ranges over all `I : Finset (Fin n)`. -/
theorem equation_4 {n k : ℕ} (g : (Fin k → ℝ) → EReal) (A : Matrix (Fin k) (Fin n) ℝ)
    (c : Fin n → ℝ) (Iplus : Set (Fin n)) :
    (∀ I : Finset (Fin n), VI g A c Iplus I ⊆ Q g A c Iplus) ∧
      Q g A c Iplus = ⋃ I : Finset (Fin n), VI g A c Iplus I := by sorry

end LowRankIndicator
