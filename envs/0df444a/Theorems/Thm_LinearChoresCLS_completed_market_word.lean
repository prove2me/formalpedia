-- Prove2me | Theorems.Thm_LinearChoresCLS_completed_market_word
-- name    : LinearChoresCLS.completed_market_word
-- status  : Open
-- author  : @Weiqiang
-- created : 2026-11-13T20:43:47.085994+00:00
-- url     : https://prove2.me/theorems/96f2333b-356a-4c11-9e2f-ffd048a3f88b
-- title:
--   Polynomial-time serialization of the completed rational market
-- statement:
--   Given a positive-dimensional rational quadratic instance $(P,\varepsilon)$ with $\varepsilon>0$, the market construction in Figure 1 has a polynomial-time bit-string implementation. Its output is the public encoding of a rational market $G$. There are bijections from the named agents and chores of the construction to the rows and columns of $G$ under which every disutility, earning requirement and supply equals the specified datum. The first $n+1$ columns are the reference chore and the coordinate chores in increasing order. This fixes the locations needed by the price decoder.
-- source:
--   Liu, Ma, Tao, Yang, and Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589v1. https://arxiv.org/html/2611.06589v1 Figure 1 and Section 7.1, Market Specification and Completing the Verification.

import Definitions.Def_LinearChoresCLS_PriceFamily
import Definitions.Def_LinearChoresCLS_ChoresSearch

namespace LinearChoresCLS

open NetworkEquilibriumCLS.LinearNash in
theorem completed_market_word :
    ∃ f : List Bool → List Bool, PolyTime f ∧
      ∀ {n : ℕ}, 0 < n → ∀ (P : Quadratic n) (ε : ℚ), 0 < ε →
        let L := chainLength P ε
        let F := completedMarket P ε
        ∃ (a m : ℕ) (e : Agent n L ≃ Fin a) (d : Chore n L ≃ Fin m) (G : RatChoresMarket a m),
          (∀ j : Fin (n+1), (d (Sum.inl j)).val = j.val) ∧
          (∀ i j, (G.disutil (e i) (d j) : ℝ) = F.disutil i j) ∧
          (∀ i, (G.earn (e i) : ℝ) = F.earn i) ∧
          (∀ j, (G.supply (d j) : ℝ) = F.supply j) ∧
          encChores G = f (encQuadratic P ++ encRat ε) := by sorry

end LinearChoresCLS
