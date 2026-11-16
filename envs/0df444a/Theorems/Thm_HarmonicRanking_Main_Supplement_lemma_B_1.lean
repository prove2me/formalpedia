-- Prove2me | Theorems.Thm_HarmonicRanking_Main_Supplement_lemma_B_1
-- name    : HarmonicRanking.Main.Supplement.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:50:24.144808+00:00
-- url     : https://prove2.me/theorems/ffca6a8c-3503-4b6f-b387-52edea5942a5
-- title:
--   Lemma B.1 — exact partial balance dual
-- statement:
--   Fix $m\ge1$. Then
--
--   $$\mathrm{val}\big(\mathrm{polyLP}'(m)\big)=\sup_{F\in D_m}R_m(F),$$
--
--   where $D_m=\{F\in\mathbb R^{m\times m}:F_{\ell r}+F_{r\ell}=1\}$ and $R_m(F)\in[-\infty,\infty)$ is the fixed-price value (55) over the region $C_m$ without the transpose-balance equations.
--
--   Dualizing only the transpose-balance equations (54) of the Mahdian–Yan program loses nothing; the multipliers become a complementary price table.
--
--   **Formalization Note** Both sides are extended reals: $R_m(F)=-\infty$ for tables with a negative entry, and the supremum is taken in `EReal`.
--
--   Differences from the source:
--   - encoding: one-based indices ℓ, r, p ∈ [m] → zero-based Fin m indices; reason: Lean convention, same programs
--   - encoding: val(polyLP′(m)), R_m(F) ∈ [−∞, ∞) and the supremum → EReal infima and supremum over the same sets; reason: same values, with −∞ representable
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 32, Lemma B.1

import Definitions.Def_HarmonicRanking_Main_Supplement_PriceLP

set_option autoImplicit false

namespace HarmonicRanking.Main.Supplement

theorem lemma_B_1 (m : ℕ) (hm : 1 ≤ m) :
    lpValue m = ⨆ (F : Fin m → Fin m → ℝ) (_ : InD F), Rm F := by sorry

end HarmonicRanking.Main.Supplement
