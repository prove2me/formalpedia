-- Prove2me | Theorems.Thm_HarmonicRanking_Main_Supplement_lemma_A_2
-- name    : HarmonicRanking.Main.Supplement.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:48:19.298662+00:00
-- url     : https://prove2.me/theorems/e7f3e4e9-8adb-497e-87c9-7717ed15c243
-- title:
--   Lemma A.2 — transpose-overlap removal
-- statement:
--   Fix $m\ge1$. For every table $g\in K_m$,
--
--   $$\min_{(c,d)\in P^\perp_m}\Phi_g(c,d)=\min_{c,d\in B_m}\Phi_g(c,d).$$
--
--   Here $K_m$ is the full class of complementary tables ($g(i,1)\ge0$, nondecreasing in the second index, $g(i,r)+g(r,i)=1$, $g(i,0)=0$), $B_m$ the set of monotone paths ending at $m$, $\Phi_g$ the two-path functional (45), and $P^\perp_m$ the transpose-overlap-free pairs of Lemma A.1.
--
--   The restriction to transpose-overlap-free pairs created by the reflection of Lemma A.1 therefore costs nothing; Corollary A.3 ($\gamma_{UW,m}=V_m$) follows from the two lemmas.
--
--   **Formalization Note** Both minima are infima in `EReal` over finite nonempty sets.
--
--   Differences from the source:
--   - encoding: one-based indices i ∈ [m] and paths (a_0,…,a_m) → zero-based Fin m and Fin (m+1) indices, with the boundary values ĝ_{i,m+1} = 0 and g(i,0) = 0 supplied by accessors; reason: Lean convention, same tables and paths
--   - encoding: min over finite sets → EReal infimum over the same finite nonempty sets; reason: a finite nonempty infimum is attained, so it is the minimum
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 30, Lemma A.2

import Definitions.Def_HarmonicRanking_Main_Supplement_GridGames

set_option autoImplicit false

namespace HarmonicRanking.Main.Supplement

theorem lemma_A_2 (m : ℕ) (hm : 1 ≤ m) (g : Fin m → Fin m → ℝ)
    (hg : IsKTable g) :
    transposeFreeMin g = twoPathMin g := by sorry

end HarmonicRanking.Main.Supplement
