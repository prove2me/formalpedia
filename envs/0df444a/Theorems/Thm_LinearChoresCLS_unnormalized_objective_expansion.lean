-- Prove2me | Theorems.Thm_LinearChoresCLS_unnormalized_objective_expansion
-- name    : LinearChoresCLS.unnormalized_objective_expansion
-- status  : Open
-- author  : @Weiqiang
-- created : 2026-11-13T20:44:01.254744+00:00
-- url     : https://prove2.me/theorems/806ab69e-ed36-42c1-a89c-eac4a7e39afb
-- title:
--   Unnormalized objective of the completed market with explicit remainders
-- statement:
--   For a positive-dimensional rational quadratic instance $P$ and tolerance $\varepsilon>0$, let $t,L$ be the completed-market parameters, $p(x)$ the unnormalized price family, and $\alpha=\lambda t^2$. There is a constant $C$ independent of $x$ such that on the unit cube
--   $$\Psi(p(x))= C+\alpha Q(x)+R_0(x)-\sum_{j<j'}R_{(j,j')}(x)+R_{\rm lin}(x).$$
--   The three remainders denote the explicit basic-market, gadget-chain and linear-correction formulas. The identity precedes the final price normalization and is the objective calculation used in the proof of Lemma 7.6.
-- source:
--   Liu, Ma, Tao, Yang, and Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589v1. https://arxiv.org/html/2611.06589v1 Sections 5 and 6.4, equation (6.18), and Section 7.3.

import Definitions.Def_LinearChoresCLS_Remainders
import Definitions.Def_LinearChoresCLS_BasicMarket

namespace LinearChoresCLS

open Finset NetworkEquilibriumCLS.LinearNash in
theorem unnormalized_objective_expansion {n : ℕ} (hn : 0 < n) (P : Quadratic n) (ε : ℚ) (hε : 0 < ε) :
    let t := tParam P ε
    let L := chainLength P ε
    ∃ C : ℝ, ∀ x, InCube x →
      (completedMarket P ε).Psi (completedPrice P ε x) =
        C + alpha P t * quadraticValue P x +
          (R0 t x - ∑ π : Pair n, chainRem P t L π x + Rlin P t x) := by sorry

end LinearChoresCLS
