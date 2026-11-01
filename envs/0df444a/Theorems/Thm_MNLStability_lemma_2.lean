-- Prove2me | Theorems.Thm_MNLStability_lemma_2
-- name    : MNLStability.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:41.674887+00:00
-- url     : https://prove2.me/theorems/7d9508cd-7997-49e4-b1ac-bcef38531d74
-- title:
--   Lemma 2 — among equal-weight products the better-stocked one has larger unit probabilities
-- statement:
--   Let $i_1\ne i_2$ be two products with equal preference weights $w_{i_1}=w_{i_2}$, and let $U$ be an inventory vector with $U_{i_1}\ge U_{i_2}$. Then for every unit index $1\le u\le U_{i_2}$,
--
--   $$\Pr\bigl[I^U_{(i_1,u)}=1\bigr]\ \ge\ \Pr\bigl[I^U_{(i_2,u)}=1\bigr].$$
--
--   The comparison underlies the exchange argument of Lemma 6 and the bounds of Claims 1 and 2.
--
--   Differences from the source:
--   - encoding: the number of customers M, finitely supported (p.3) → a law pM : ℕ →₀ ℝ (IsLaw) mixed over its support; reason: Lean convention; same instances
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Lemma 2, p.12; proof App. A.1, p.43

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_prob

namespace MNLStability

/-- **Lemma 2** (SSRN:3498325, p.12; proof App. A.1, p.43). Let `i₁ ≠ i₂` be a pair of products with
`w_{i₁} = w_{i₂}` and `U_{i₁} ≥ U_{i₂}`. Then, for every `u ≤ U_{i₂}`,
`Pr[I^U_{(i₁,u)} = 1] ≥ Pr[I^U_{(i₂,u)} = 1]`. -/
theorem lemma_2 {n : ℕ} (wts : Weights n) (hw : wts.Pos) (pM : ℕ →₀ ℝ) (hM : IsLaw pM)
    (U : Fin n → ℕ) (i₁ i₂ : Fin n) (hne : i₁ ≠ i₂) (hw₁₂ : wts.w i₁ = wts.w i₂)
    (hU : U i₂ ≤ U i₁) (u : ℕ) (hu1 : 1 ≤ u) (hu : u ≤ U i₂) :
    unitProb wts pM U i₂ u ≤ unitProb wts pM U i₁ u := by sorry

end MNLStability
