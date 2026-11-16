-- Prove2me | Theorems.Thm_HarmonicRanking_Main_Supplement_theorem_7_1
-- name    : HarmonicRanking.Main.Supplement.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:48:47.269206+00:00
-- url     : https://prove2.me/theorems/27a7f0a8-1333-4b61-92d8-6d69c7461fbb
-- title:
--   Theorem 7.1 — exact finite-grid value correspondence $\gamma_{UW,m}=V_m=\mathrm{val}(\mathrm{polyLP}'(m))$
-- statement:
--   For every grid size $m\ge1$,
--
--   $$\gamma_{UW,m}=V_m=\mathrm{val}\big(\mathrm{polyLP}'(m)\big).\tag{42}$$
--
--   Here $\gamma_{UW,m}=\max_{\hat g\in\mathfrak G_{\mathrm{comp},m}}\min_{(a,b)\in T_{UW,m}}\hat\Gamma_m(\hat g,a,b)$ is the exact whole-cell unweighted value (44), whose outer maximum ranges over all complementary monotone tables, not only score-balanced ones; $V_m=\max_{g\in K_m}\min_{a,b\in B_m}\Phi_g(a,b)$ is the reflected complementary two-path value (46); and $\mathrm{val}(\mathrm{polyLP}'(m))$ is the optimal value of the Mahdian–Yan program (49)–(54). Both outer maxima are attained.
--
--   The identity is exact at every fixed grid size: the complementary primal–dual (gain-sharing) formulation of the unweighted endpoint has the same value as the Mahdian–Yan factor-revealing program behind the earlier $0.696$ analysis of random-arrival Ranking.
--
--   **Formalization Note** The three values are suprema and infima in `EReal` computed from the data of Appendix A; the conclusion also asserts that the suprema defining $\gamma_{UW,m}$ and $V_m$ are attained, which is what the source's "max" asserts.
--
--   Differences from the source:
--   - encoding: one-based indices i ∈ [m] and paths (a_0,…,a_m) → zero-based Fin m and Fin (m+1) indices, with the boundary values ĝ_{i,m+1} = 0 and g(i,0) = 0 supplied by accessors; reason: Lean convention, same tables and paths
--   - encoding: max/min in (44), (46) and the optimal value val → EReal suprema and infima over the same sets, with attainment of both outer maxima stated as conclusions; reason: same values; the inner minima are over finite nonempty sets and the attainment clauses express the source's max
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 23, Theorem 7.1, eq. (42) (definitions pp. 28–31, eqs. (43)–(46), (49)–(54))

import Definitions.Def_HarmonicRanking_Main_Supplement_PriceLP

set_option autoImplicit false

namespace HarmonicRanking.Main.Supplement

theorem theorem_7_1 (m : ℕ) (hm : 1 ≤ m) :
    gammaUW m = Vval m ∧ Vval m = lpValue m ∧
    (∃ gh : Fin m → Fin m → ℝ, IsCompTable gh ∧ wholeCellMin gh = gammaUW m) ∧
    (∃ g : Fin m → Fin m → ℝ, IsKTable g ∧ twoPathMin g = Vval m) := by sorry

end HarmonicRanking.Main.Supplement
