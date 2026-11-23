-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_gameValueInf_le_gameValueB1Inf
-- name    : GrothendieckPD.Digits.gameValueInf_le_gameValueB1Inf
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:14:34.403806+00:00
-- url     : https://prove2.me/theorems/273266af-9c5e-4a43-b04c-903c4ecbe607
-- title:
--   Boolean game values are bounded by the Appendix B game values
-- statement:
--   For every real coefficient sequence $q=(q_m)_{m\ge0}$, let $v_\infty(q)$ be the Hermite projection game value over measurable $\pm1$-valued pairs, and let $v_\infty^{(B.1)}(q)$ be the value in Eq. (B.1), over measurable $[-1,1]$-valued pairs with an absolute value around the payoff. Then
--
--   $$
--   v_\infty(q)\le v_\infty^{(B.1)}(q).
--   $$
--
--   This comparison connects the Boolean game appearing in Theorem 4.1 with the relaxed game estimated in Lemma B.1. The suprema range over all finite Gaussian dimensions, as in the published definitions.
--
--   **Formalization Note** The two values are respectively `gameValueInf q` and `gameValueB1Inf q`; measurable sign functions are part of the unit-bounded class, and $x\le |x|$ supplies the payoff comparison.
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Theorem 4.1 and its proof, p. 11, using the Boolean game definition in §2.1, p. 3 and the unit-bounded game in Eq. (B.1), p. 19

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames

/-- The Boolean Hermite projection game value is at most the unit-bounded,
absolute-value game value used in Eq. (B.1). -/
theorem GrothendieckPD.Digits.gameValueInf_le_gameValueB1Inf (q : ℕ → ℝ) :
    gameValueInf q ≤ gameValueB1Inf q := by sorry
