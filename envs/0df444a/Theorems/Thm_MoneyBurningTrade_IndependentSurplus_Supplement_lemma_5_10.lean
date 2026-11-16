-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_Supplement_lemma_5_10
-- name    : MoneyBurningTrade.IndependentSurplus.Supplement.lemma_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:44:31.03202+00:00
-- url     : https://prove2.me/theorems/1f9662d4-14d3-40cd-8ea4-b542891bb9ed
-- title:
--   Lemma 5.10 — first-best social welfare under F^n
-- statement:
--   Let $n\ge4$, $R=\sqrt n$, $q_i=R^{i-n}$, $Z=\sum_{r=1}^n1/q_r$, and let $F=F^n$ put probability $1/(Zq_i)$ on $(q_{i-1},q_i)$, $i\in[n]$. Then the first-best social welfare is
--
--   $$\mathrm{SW}_{\mathrm{OPT}}(F)=\mathbb E_F[\max\{v_s,v_b\}]=\frac nZ.$$
--
--   With Lemmas 5.7 and 5.8 this yields the ratio bound $1/R+5R/n=6/\sqrt n$ of Theorem 5.2.
--
--   Differences from the source:
--   - encoding: the fixed integer n ≥ 4 of the proof of Theorem 5.2, chosen with 6/√n < ε → every natural number n ≥ 4; reason: the lemma does not involve ε and every n ≥ 4 meets 6/√n < ε for some ε > 0; the same instances
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 5.10; §5.2; proof in Appendix A.14, printed p. 34 (PDF p. 35); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_JointObjectives
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_GeometricLaw

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- Lemma 5.10, §5.2 p.34: for every integer `n ≥ 4`, the first-best social welfare
under `F^n` is `SW_OPT(F) = n / Z`. -/
theorem lemma_5_10 (n : ℕ) (hn : 4 ≤ n) :
    firstBestSW (geomLaw n) = (n : ℝ) / geomZ n := by sorry

end MoneyBurningTrade.IndependentSurplus.Supplement
