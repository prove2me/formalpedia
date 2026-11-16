-- Prove2me | Theorems.Thm_HarmonicRanking_Main_Supplement_theorem_B_7
-- name    : HarmonicRanking.Main.Supplement.theorem_B_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:52:32.881881+00:00
-- url     : https://prove2.me/theorems/11ff5c98-4c28-460f-bcf6-70fb05e2f758
-- title:
--   Theorem B.7 — monotone-price normalization
-- statement:
--   Fix $m\ge1$. Then
--
--   $$\max_{F\in A_m}R_m(F)=\sup_{F\in D_m}R_m(F)=\mathrm{val}\big(\mathrm{polyLP}'(m)\big):$$
--
--   the supremum of the fixed-price value $R_m$ over all complementary tables $D_m$ is attained at a monotone price table $F\in A_m$, and it equals the optimal value of the Mahdian–Yan program.
--
--   With Theorem B.3 this yields $V_m=\mathrm{val}(\mathrm{polyLP}'(m))$, the second equality of Theorem 7.1.
--
--   **Formalization Note** The first equality is stated as `IsGreatest` of the image of $A_m$ under $R_m$ at the value $\sup_{F\in D_m}R_m(F)$ (taken in `EReal`), which includes attainment of the maximum.
--
--   Differences from the source:
--   - encoding: one-based indices ℓ, r, p ∈ [m] → zero-based Fin m indices; reason: Lean convention, same programs
--   - encoding: max over A_m, sup over D_m and val → IsGreatest of the image of A_m at the EReal supremum over D_m, and EReal infimum for val; reason: same statement, attainment of the max included
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 43, Theorem B.7

import Definitions.Def_HarmonicRanking_Main_Supplement_PriceLP

set_option autoImplicit false

namespace HarmonicRanking.Main.Supplement

theorem theorem_B_7 (m : ℕ) (hm : 1 ≤ m) :
    IsGreatest (Rm '' {F : Fin m → Fin m → ℝ | InA F})
      (⨆ (F : Fin m → Fin m → ℝ) (_ : InD F), Rm F) ∧
    (⨆ (F : Fin m → Fin m → ℝ) (_ : InD F), Rm F) = lpValue m := by sorry

end HarmonicRanking.Main.Supplement
