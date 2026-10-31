-- Prove2me | Theorems.Thm_LeaderStyle_WageFloor_lemma_4
-- name    : LeaderStyle.WageFloor.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:23.056431+00:00
-- url     : https://prove2.me/theorems/2da1a55d-3fe1-4d5c-bc6e-f632bcb9030f
-- title:
--   Lemma 4, p. 17 (PDF 19), corrected reading — FU beats 0, U and F iff (F) and (U)
-- statement:
--   Under the corrected reading of Lemma 4, style FU is strictly cheaper than each of pure monetary incentives, conditional praise, and conditional scolding exactly when both (F) and (U) hold:
--
--   $$\bigl(C_{FU}<C_0\ \wedge\ C_{FU}<C_U\ \wedge\ C_{FU}<C_F\bigr)\iff\bigl(k_F^h<r\ \wedge\ (U)\bigr).$$
--
--   These conditions imply noncompetitive wage-setting, $\underline u<\underline w$. The result combines the two strict improvement tests used in the optimal-style classification.
--
--   **Formalization Note** The printed first sentence alone, $C_{FU}<C_0$ iff (F) and (U), is false: with $\rho=1/2$, $c=10$, $r=5$, $s=1$, all leadership costs $1$, $\underline u=0$, $\underline w=-10$, and $\underline u_l=0$, one has $C_{FU}=9<C_0=10$ while (U) fails. The formal item follows the preceding §4.4 paragraph, which compares FU with all three alternatives. The printed rent and welfare clauses are outside this item.
-- source:
--   Dur, Kvaløy & Schöttner, Leadership Styles and Labor-Market Conditions, CRC TRR 190 Discussion Paper No. 278 (26 Feb 2021), p. 17 (PDF 19), Lemma 4, p. 17 (PDF 19), corrected reading

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model

namespace LeaderStyle.WageFloor

theorem lemma_4 (P : Params) (hS : P.Standing) :
    ((Prefers P .FU .none ∧ Prefers P .FU .U ∧ Prefers P .FU .F) ↔
      (condF P ∧ condU P)) ∧
      (condF P ∧ condU P → P.ur < P.wf) := by sorry
end LeaderStyle.WageFloor
