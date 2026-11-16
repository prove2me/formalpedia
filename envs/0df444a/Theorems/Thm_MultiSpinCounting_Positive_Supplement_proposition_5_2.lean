-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_Supplement_proposition_5_2
-- name    : MultiSpinCounting.Positive.Supplement.proposition_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:26:48.414228+00:00
-- url     : https://prove2.me/theorems/bc3016d9-df1a-455e-8094-ee35c13dd410
-- title:
--   Proposition 5.2 (used in the proof of Theorem 1.7) — permissive-block feasibility and mass
-- statement:
--   Let $\Phi=(G_\Phi,L_\Phi)$ be any feasible finite list-coloring instance with lists contained in a palette of $q$ colors. Let $B$ be a connected block such that every edge $(u,v)$ crossing from $B$ to its complement satisfies $|L_\Phi(v)|>\deg_{G_\Phi}(v)+1$. For every proper partial list-coloring $\sigma$ of $B$, there exists a full proper list-coloring extending $\sigma$, and its uniform marginal probability obeys
--   $$\mu_\Phi(B\leftarrow\sigma)\ge 2^{-|\partial_E B|}q^{-|B|}.$$
--   The exponent $|\partial_E B|$ counts edges, and every degree is in the current graph. The theorem supplies both feasibility and a positive lower bound for block marginals.
--
--   Differences from the source:
--   - encoding: a finite list-coloring instance and a connected block B → the actual carrier Fin n and assignments on the subtype B; reason: every finite current instance has this form; no extendability is assumed
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 19, Proposition 5.2

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Supplement_ListBlocks

namespace MultiSpinCounting.Positive.Supplement

/-- Proposition 5.2, p. 19: extension and the edge-boundary lower bound. -/
theorem proposition_5_2 {n q : ℕ} (Φ : ListInstance n q) (hΦ : Feasible Φ)
    (B : Finset (Fin n)) (hB : Permissive Φ B) (σ : B → Fin q)
    (hσ : PartialProper Φ B σ) :
    (∃ τ ∈ listColorings Φ, ∀ u : B, τ u.val = σ u) ∧
    (2 : ℝ) ^ (-((boundaryEdges Φ B).card : ℤ)) *
      (q : ℝ) ^ (-(B.card : ℤ)) ≤ blockMarginal Φ B σ := by sorry

end MultiSpinCounting.Positive.Supplement
