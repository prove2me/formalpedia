-- Prove2me | Theorems.Thm_HarmonicRanking_Main_Supplement_lemma_B_5
-- name    : HarmonicRanking.Main.Supplement.lemma_B_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:51:32.34069+00:00
-- url     : https://prove2.me/theorems/49de61a4-16f9-432b-9c7a-d1d62dd520ae
-- title:
--   Lemma B.5 — interval-order minimax
-- statement:
--   Fix $m\ge1$. Let $I_m=\{[\ell,r]:1\le\ell<r\le m\}$, ordered by inclusion, and for a table $F$ let $h_I=2F_{\ell r}-1$ for $I=[\ell,r]$.
--
--   1. The map $F\mapsto(h_I)_{I\in I_m}$ is a bijection from $A_m$ onto the order polytope
--   $$0\le h_I\le1,\qquad I\subseteq J\implies h_I\le h_J.$$
--   2. The maximum $V^A_m:=\max_{F\in A_m}R_m(F)$ is attained, and
--   $$V^A_m=\min_{(x,y)\in\hat C_m}\frac1{m^2}\Big[\sum_{\ell,r}M_{\ell r}+\sigma(\delta)\Big],\tag{76}$$
--   the minimum being attained as well. Here $M_{\ell r}=\sum_p m\,x(\ell,r,p)$, $\delta_I=M_{\ell r}-M_{r\ell}$ for $I=[\ell,r]$, and $\sigma(\delta)=\max_U\sum_{I\in U}\delta_I$ over upward-closed families $U\subseteq I_m$; the factor $1/m^2$ multiplies $\sigma(\delta)$ as well.
--
--   The monotone-price maximization thus becomes an explicit minimization over the capped region, with an imbalance penalty given by the interval order.
--
--   **Formalization Note** Attainment is expressed by `IsGreatest` for the image of $A_m$ under $R_m$ and `IsLeast` for the image of $\hat C_m$ under the objective of (76), with a common real value.
--
--   Differences from the source:
--   - encoding: one-based indices ℓ, r, p ∈ [m] → zero-based Fin m indices; reason: Lean convention, same programs
--   - encoding: max/min in (76) and in V^A_m → IsGreatest and IsLeast of the images, with a common real value; reason: same statement, attainment included
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 38, Lemma B.5, eqs. (74)–(76)

import Definitions.Def_HarmonicRanking_Main_Supplement_PriceLP

set_option autoImplicit false

namespace HarmonicRanking.Main.Supplement

theorem lemma_B_5 (m : ℕ) (hm : 1 ≤ m) :
    Set.BijOn (intervalCoords (m := m)) {F | InA F} {h | InOrderPolytope h} ∧
    ∃ v : ℝ, IsGreatest (Rm '' {F : Fin m → Fin m → ℝ | InA F}) (v : EReal) ∧
      IsLeast (minimaxObjective '' {x : Fin m → Fin m → Fin m → ℝ | InCcap x}) v := by sorry

end HarmonicRanking.Main.Supplement
