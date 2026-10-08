-- Prove2me | Theorems.Thm_OceanicGames_Limit_equation_3_5
-- name    : OceanicGames.Limit.equation_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:55.034376+00:00
-- url     : https://prove2.me/theorems/94e0f0a2-d010-4671-aa41-2e2129fd2ede
-- title:
--   Equations (3.5)–(3.6) — volume of a pivotal predecessor cell
-- statement:
--   Let $S\subseteq M\setminus\{i\}$, $s=|S|$, and assume nonnegative major weights and $\alpha>0$. Define
--
--   $$t_1=\left\langle\frac{c-w(S\cup\{i\})}{\alpha}\right\rangle,\qquad t_2=\left\langle\frac{c-w(S)}{\alpha}\right\rangle,$$
--
--   where $\langle\cdot\rangle$ clamps a real number to $[0,1]$. Then
--
--   $$\mu^m(A_i\cap B_{i,S})=\int_{[t_1,t_2]}t^s(1-t)^{m-s-1}\,dt.$$
--
--   The identity calculates each cell's volume and supplies the integral terms in the oceanic formula.
--
--   **Formalization Note** The integral is over a closed set; its boundary has zero Lebesgue measure. The condition $S\subseteq M\setminus\{i\}$ makes the natural-number exponent $m-s-1$ equal to the paper's integer exponent.
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), §3 (3.5)–(3.6), pp. 8–9; https://www.rand.org/pubs/research_memoranda/RM2649.html

import Mathlib
import Definitions.Def_OceanicGames_Limit_Basic

namespace OceanicGames.Limit

open MeasureTheory Set Finset

/-- Equations (3.5)–(3.6): integrate the volume of a predecessor cell
over the pivotal interval for player i. -/
theorem equation_3_5 {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ) (i : Fin m)
    (S : Finset (Fin m)) (hS : S ⊆ Finset.univ.erase i)
    (hc : 0 ≤ c) (halpha : 0 < alpha) (hw : ∀ j, 0 ≤ w j) :
    (volume (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S)).toReal =
      ∫ t in Set.Icc
        (clamp01 ((c - OceanicGames.Interior.wsum w (insert i S)) / alpha))
        (clamp01 ((c - OceanicGames.Interior.wsum w S) / alpha)),
        t ^ S.card * (1 - t) ^ (m - S.card - 1) := by sorry

end OceanicGames.Limit
