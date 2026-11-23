-- Prove2me | Theorems.Thm_LinearChoresCLS_completedRatMarket_word
-- name    : LinearChoresCLS.completedRatMarket_word
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:59:07.904796+00:00
-- url     : https://prove2.me/theorems/76ae79c6-a0de-4903-a626-e1b412c37b4d
-- title:
--   The canonical `Fin`-indexed completed market is serializable in polynomial time
-- statement:
--   There is one polynomial-time Cook-machine word map which, on every positive-dimensional quadratic $P$ and rational tolerance $\varepsilon>0$, returns the binary encoding of the canonical `Fin`-indexed rational completed market:
--   $$
--   f(\operatorname{enc}P\,\|\,\operatorname{enc}\varepsilon)
--    =\operatorname{encChores}(\operatorname{completedRatMarket}P\varepsilon).
--   $$
--   This is the computational content of Section 7.1, p.32: $L$ and all entry lengths are polynomially bounded, and the explicit market specification in items (i)–(iv) can consequently be written out in polynomial time. The input word is unconstrained outside valid encoded instances.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Section 7.1 (i)–(iv), p.31, and “Since $L$ and the encoding lengths of all entries are polynomially bounded … the market can be constructed in polynomial time,” p.32.

import Definitions.Def_LinearChoresCLS_EncodedMarket

namespace LinearChoresCLS

open NetworkEquilibriumCLS.LinearNash in
theorem completedRatMarket_word :
    ∃ f : List Bool → List Bool, PolyTime f ∧
      ∀ {n : ℕ}, 0 < n → ∀ (P : Quadratic n) (ε : ℚ), 0 < ε →
        encChores (completedRatMarket P ε) = f (encQuadratic P ++ encRat ε) := by sorry
