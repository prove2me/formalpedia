-- Prove2me | Theorems.Thm_HarmonicRanking_Main_Supplement_lemma_B_4
-- name    : HarmonicRanking.Main.Supplement.lemma_B_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:50:56.46831+00:00
-- url     : https://prove2.me/theorems/03954cef-ff84-4de7-816c-ab2e1a7fc6d1
-- title:
--   Lemma B.4 — compact price domain
-- statement:
--   Fix $m\ge1$.
--
--   1. For an arbitrary real table $F$,
--   $$R_m(F)>-\infty\iff F_{\ell r}\ge0\quad(\ell,r\in[m]).$$
--   2. Consequently, for $F\in D_m$, $R_m(F)$ is finite if and only if $0\le F\le1$ entrywise.
--   3. For every $F\ge0$, the infimum defining $R_m(F)$ is unchanged if one additionally imposes $0\le y(\ell,r,p)\le1/m$, i.e. the infimum over the capped region $\hat C_m$ equals $R_m(F)$.
--
--   This restricts the price maximization of Lemma B.1 to the compact box $0\le F\le1$ and the primal minimization to a compact region, as needed for the minimax argument of Lemma B.5.
--
--   **Formalization Note** $R_m$ is `EReal`-valued and $-\infty$ is `⊥`; "finite" in clause 2 means neither `⊥` nor `⊤`.
--
--   Differences from the source:
--   - encoding: one-based indices ℓ, r, p ∈ [m] → zero-based Fin m indices; reason: Lean convention, same programs
--   - encoding: R_m(F) ∈ [−∞, ∞), "R_m(F) > −∞", "finite", and the infimum with the cap 0 ≤ y ≤ 1/m → EReal infima R_m and RmCapped, ⊥ < R_m F, R_m F ≠ ⊥ ∧ R_m F ≠ ⊤; reason: same values, with −∞ representable
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 37, Lemma B.4

import Definitions.Def_HarmonicRanking_Main_Supplement_PriceLP

set_option autoImplicit false

namespace HarmonicRanking.Main.Supplement

theorem lemma_B_4 (m : ℕ) (hm : 1 ≤ m) :
    (∀ F : Fin m → Fin m → ℝ, ⊥ < Rm F ↔ ∀ ℓ r, 0 ≤ F ℓ r) ∧
    (∀ F : Fin m → Fin m → ℝ, InD F →
      (Rm F ≠ ⊥ ∧ Rm F ≠ ⊤ ↔ ∀ ℓ r, 0 ≤ F ℓ r ∧ F ℓ r ≤ 1)) ∧
    (∀ F : Fin m → Fin m → ℝ, (∀ ℓ r, 0 ≤ F ℓ r) → RmCapped F = Rm F) := by sorry

end HarmonicRanking.Main.Supplement
