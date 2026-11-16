-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_Supplement_lemma_6_2
-- name    : IntervalMaxCutEPTAS.Scheme.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:32:00.493484+00:00
-- url     : https://prove2.me/theorems/3a581324-1ac2-46f3-a5bb-6430bf3afad2
-- title:
--   Lemma 6.2 (used in the proof of Theorem 1.2) — external neighborhood classes
-- statement:
--   In the same good-shift hierarchy with $b\ge4$ and $\sigma=2^{-b}$, every nonroot cell satisfies
--
--   $$K(C)\le(2|P(C)|+1)^2\le(20b/\sigma+1)^2,\qquad K(\mathrm{root})\le1.$$
--
--   Here $K(C)$ counts distinct actual external neighbor sets of vertices in $V_C$ and is zero for an empty $V_C$. Both inequalities and the separate root bound are included. The lemma supplies the class bound used for the width construction.
--
--   Differences from the source:
--   - encoding: the structure fixed in Proposition 4.10 with b ≥ 4 and its good shift → the published Setup, valid heap cell indices, group representative ids and GoodShift; reason: these are the same constructed objects and standing assumptions; no geometric or density condition is added
--   - encoding: K(C) counts distinct external neighbor sets → the finite image of actual neighbor sets, with cardinality zero on empty VC; reason: all source instances and the root case are retained
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 6.2, PDF p. 23 (printed p. 22)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_Endpoints

set_option autoImplicit false

namespace IntervalMaxCutEPTAS.Scheme.Supplement

/-- Lemma 6.2, PDF 23 (printed 22), including both inequalities and the root. -/
theorem lemma_6_2 {n : ℕ} (P : Setup n) (hb : 4 ≤ P.b)
    (hθ : P.θ < 2 * bigM n) (hshift : GoodShift P) :
    (∀ C, IsCell n C → C ≠ 1 →
      neighborhoodCount P C ≤ (2 * (ancestralPositions P C).card + 1) ^ 2 ∧
      (((2 * (ancestralPositions P C).card + 1) ^ 2 : ℕ) : ℝ) ≤
        (20 * P.b / sigma P.b + 1) ^ 2) ∧
    neighborhoodCount P 1 ≤ 1 := by sorry

end IntervalMaxCutEPTAS.Scheme.Supplement
