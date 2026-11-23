-- Prove2me | Theorems.Thm_HarmonicRanking_Main_Supplement_theorem_B_3
-- name    : HarmonicRanking.Main.Supplement.theorem_B_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T14:49:44.974749+00:00
-- url     : https://prove2.me/theorems/15c757e3-5c2a-43be-804b-450fbb3afd14
-- title:
--   Theorem B.3 — fixed-price contraction
-- statement:
--   Fix $m\ge1$ and a monotone price table $F\in A_m$. Define $g(i,q):=F_{m+1-q,\,m+1-i}$ for $i,q\in[m]$, with $g(i,0):=0$. Then
--
--   $$R_m(F)=\min_{a,b\in B_m}\Phi_g(a,b),$$
--
--   where $R_m(F)=\inf_{(x,y)\in C_m}\frac2m\sum_{\ell,r,p}F_{\ell r}x(\ell,r,p)$ is the fixed-price value (55) over the region $C_m$ (constraints (50)–(53), no transpose balance), and $\Phi_g$ is the two-path functional (45).
--
--   For a fixed monotone price the inner linear program is thus exactly the two-path game; combined with Theorem B.7 this gives $V_m=\mathrm{val}(\mathrm{polyLP}'(m))$ (Corollary B.8).
--
--   **Formalization Note** $R_m$ is an infimum in `EReal`; the right side is the `EReal` infimum over the finite nonempty set $B_m\times B_m$.
--
--   Differences from the source:
--   - encoding: one-based indices i ∈ [m] and paths (a_0,…,a_m) → zero-based Fin m and Fin (m+1) indices, with the boundary values ĝ_{i,m+1} = 0 and g(i,0) = 0 supplied by accessors; reason: Lean convention, same tables and paths
--   - encoding: min over finite sets → EReal infimum over the same finite nonempty sets; reason: a finite nonempty infimum is attained, so it is the minimum
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 37, Theorem B.3 (definitions pp. 28, 32, eqs. (45), (55)–(56))

import Definitions.Def_HarmonicRanking_Main_Supplement_PriceLP

set_option autoImplicit false

namespace HarmonicRanking.Main.Supplement

theorem theorem_B_3 (m : ℕ) (hm : 1 ≤ m) (F : Fin m → Fin m → ℝ)
    (hF : InA F) :
    Rm F = twoPathMin (priceReflect F) := by sorry

end HarmonicRanking.Main.Supplement
