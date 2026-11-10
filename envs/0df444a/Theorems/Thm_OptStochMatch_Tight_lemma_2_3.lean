-- Prove2me | Theorems.Thm_OptStochMatch_Tight_lemma_2_3
-- name    : OptStochMatch.Tight.lemma_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:53:36.022528+00:00
-- url     : https://prove2.me/theorems/7a460c62-4e17-4db9-b778-930a6e2abb08
-- title:
--   Lemma 2.3 — flow decomposition of the coverage polymatroid
-- statement:
--   A vector $x\in\mathbb R^m_+$ belongs to $\mathcal P_\lambda$ if and only if there are nonnegative allocations $(x_{i,S})$ with $\sum_{i\in S}x_{i,S}\le\lambda_S$ for all $S\subseteq[m]$ and $\sum_{S\ni i}x_{i,S}=x_i$ for all $i\in[m]$.
--
--   Differences from the source:
--   - encoding: allocations (x_{i,S}) indexed by i ∈ [m], S ⊆ [m] → F : Fin m → Finset (Fin m) → ℝ, nonnegative; entries with i ∉ S enter no constraint; reason: the constraints only involve i ∈ S, so the extra entries can be taken 0; same statement
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Lemma 2.3, p. 7 (PDF p. 8)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
open scoped NNReal BigOperators

namespace OptStochMatch.Tight

/-- Lemma 2.3 (p. 7, PDF 8), flow decomposition. A vector `x ∈ ℝ^m_+` lies in `P_λ` if and
only if there are nonnegative allocations `(x_{i,S})` with `∑_{i∈S} x_{i,S} ≤ λ_S` for every
`S ⊆ [m]` and `∑_{S∋i} x_{i,S} = x_i` for every `i ∈ [m]`. -/
theorem lemma_2_3 {m : ℕ} (lam : Ty m → ℝ≥0) (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i) :
    x ∈ Plam lam ↔
      ∃ F : Fin m → Ty m → ℝ, (∀ i S, 0 ≤ F i S) ∧
        (∀ S : Ty m, ∑ i ∈ S, F i S ≤ (lam S : ℝ)) ∧
        ∀ i : Fin m, ∑ S ∈ (Finset.univ.filter fun S : Ty m => i ∈ S), F i S = x i := by sorry

end OptStochMatch.Tight
