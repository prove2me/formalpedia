-- Prove2me | Theorems.Thm_MultiwayCut_lemma_5_3
-- name    : MultiwayCut.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:27.54902+00:00
-- url     : https://prove2.me/theorems/888d1d29-3150-4333-bcbb-818db9c5ede1
-- title:
--   Lemma 5.3 — $a\cdot u\ge0$ for every sorted nonnegative $u$ iff $a\succeq0$
-- statement:
--   Let $\mathbf a\in\mathbb R^k$. The following are equivalent:
--   1. $\mathbf a\cdot\mathbf u\ge0$ for every $\mathbf u\in\mathbb R^k_+$ with $u_1\ge\dots\ge u_k\ge0$;
--   2. $\mathbf a\succeq0$, i.e. $\sum_{j=1}^\ell a_j\ge0$ for every $\ell=1,\dots,k$.
--
--   It is used to remove the absolute values in (5.2) when the rows of $A$ are ordered by $\succeq$.
--
--   Differences from the source: none.
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, Lemma 5.3, p.7

import Mathlib
import Definitions.Def_MultiwayCut_Transformation

open Matrix

namespace MultiwayCut

/-- **Lemma 5.3**, Buchbinder, Schwartz & Weizman, *Simplex Transformations and the Multiway Cut
Problem*, manuscript of Nov. 1, 2016, p.7: for `a ∈ ℝᵏ` the following are equivalent:
(1) `a · u ≥ 0` for every `u ∈ ℝᵏ₊` with `u₁ ≥ … ≥ u_k ≥ 0`; (2) `a ⪰ 0` (Definition 5.1). -/
theorem lemma_5_3 {k : ℕ} (a : Fin k → ℝ) :
    (∀ u : Fin k → ℝ, Antitone u → (∀ ℓ, 0 ≤ u ℓ) → 0 ≤ a ⬝ᵥ u) ↔ PrefixGe a 0 := by sorry

end MultiwayCut
