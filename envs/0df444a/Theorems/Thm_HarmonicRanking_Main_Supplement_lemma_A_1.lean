-- Prove2me | Theorems.Thm_HarmonicRanking_Main_Supplement_lemma_A_1
-- name    : HarmonicRanking.Main.Supplement.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T14:47:33.823619+00:00
-- url     : https://prove2.me/theorems/eb4fb863-d62b-495b-ae2a-09a32fefbe71
-- title:
--   Lemma A.1 — direct whole-cell reflection
-- statement:
--   Fix $m\ge1$. For $\hat g\in\mathfrak G_{\mathrm{comp},m}$ define the reflected table $(R\hat g)(k,r):=\hat g_{m+1-k,m+1-r}$ for $k,r\in[m]$, with $(R\hat g)(k,0):=0$. Then:
--
--   1. $R$ is a bijection from $\mathfrak G_{\mathrm{comp},m}$ onto $K_m$;
--   2. for every $\hat g\in\mathfrak G_{\mathrm{comp},m}$, with $g=R\hat g$,
--   $$\min_{(a,b)\in T_{UW,m}}\hat\Gamma_m(\hat g,a,b)=\min_{(c,d)\in P^\perp_m}\Phi_g(c,d),$$
--   where $P^\perp_m=\{(c,d)\in B_m^2:X_{kr}Y_{rk}=0\text{ for all }k,r\in[m]\}$, $X_{kr}=\mathbf 1\{c_{k-1}\ge r\}$, $Y_{kr}=\mathbf 1\{d_{k-1}\ge r\}$.
--
--   Reflecting both grid coordinates turns the whole-cell unweighted game into the complementary two-path game, up to the transpose-overlap restriction removed by Lemma A.2; together they give the first equality of Theorem 7.1.
--
--   **Formalization Note** Both minima are infima in `EReal` over finite nonempty sets; the bijection is `Set.BijOn`.
--
--   Differences from the source:
--   - encoding: one-based indices i ∈ [m] and paths (a_0,…,a_m) → zero-based Fin m and Fin (m+1) indices, with the boundary values ĝ_{i,m+1} = 0 and g(i,0) = 0 supplied by accessors; reason: Lean convention, same tables and paths
--   - encoding: min over finite sets → EReal infimum over the same finite nonempty sets; reason: a finite nonempty infimum is attained, so it is the minimum
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 29, Lemma A.1 (definitions pp. 28–29, eqs. (43)–(46))

import Definitions.Def_HarmonicRanking_Main_Supplement_GridGames

set_option autoImplicit false

namespace HarmonicRanking.Main.Supplement

theorem lemma_A_1 (m : ℕ) (hm : 1 ≤ m) :
    Set.BijOn (reflect (m := m)) {gh | IsCompTable gh} {g | IsKTable g} ∧
    ∀ gh : Fin m → Fin m → ℝ, IsCompTable gh →
      wholeCellMin gh = transposeFreeMin (reflect gh) := by sorry

end HarmonicRanking.Main.Supplement
