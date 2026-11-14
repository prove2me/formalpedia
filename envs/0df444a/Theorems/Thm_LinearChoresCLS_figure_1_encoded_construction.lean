-- Prove2me | Theorems.Thm_LinearChoresCLS_figure_1_encoded_construction
-- name    : LinearChoresCLS.figure_1_encoded_construction
-- status  : Open
-- author  : @Weiqiang
-- created : 2026-11-13T20:22:13.535825+00:00
-- url     : https://prove2.me/theorems/c927bc11-e2aa-4e79-a853-02381264834e
-- title:
--   Figure 1 — polynomial-time encoding of the completed market and its price decoder
-- statement:
--   For a valid rational quadratic instance $I=(P,\varepsilon)$ of positive dimension, the completed linear chores market has strictly positive data. There are polynomial-time functions $f$ and $g$ on the mission's bit encodings with the following properties.
--
--   The word $f(I)$ is a valid rational chores-market instance. For every encoded exact rational equilibrium $y$ of $f(I)$, there is an equilibrium $(p,z)$ of the completed market on its named agents and chores. The output $g(I,y)$ encodes a rational vector $v$ satisfying
--   $$
--   v_i = \frac{1}{t}\left(\frac{p_i}{p_0}-1\right),\qquad t=2^{-L}.
--   $$
--
--   Here the real embedding of $v$ is exactly the mission's price decoder applied to $p$. The representation of $(p,z)$ on the named agents and chores accommodates the finite reindexing used by the bit-string market encoding.
--
--   **Formalization note.** This is the computational part of Figure 1. It records polynomial-time computability on Cook's machines, positivity and validity of the constructed market, and the agreement of the encoded decoder with equation (7.3). The separate analytic claim that the decoded vector satisfies the approximate KKT conditions follows from Proposition 4.1 and the Section 7 milestones. The answer condition is required for every rational equilibrium encoding, with no length restriction.
-- source:
--   Liu, Ma, Tao, Yang, and Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589v1, Section 3, Figure 1 (p. 8), Proposition 4.1 (p. 11), Section 7.1, equations (7.1)–(7.3) (pp. 30–32) and Completing the Verification (p. 38). https://arxiv.org/html/2611.06589v1

import Definitions.Def_LinearChoresCLS_PriceFamily
import Definitions.Def_LinearChoresCLS_ChoresSearch
import Definitions.Def_LinearChoresCLS_EpsKKT

open NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

theorem figure_1_encoded_construction :
    ∃ (f : List Bool → List Bool) (g : List (Option (Bool ⊕ Bool)) → List Bool),
      PolyTime f ∧ PolyTime g ∧
      ∀ (n : ℕ) (_ : 0 < n) (P : Quadratic n) (ε : ℚ) (_ : 0 < ε),
        let I := encQuadratic P ++ encRat ε
        (completedMarket P ε).Valid ∧ choresCESearch.valid (f I) ∧
        ∀ y, choresCESearch.answer (f I) y →
          ∃ (p : Chore n (chainLength P ε) → ℝ)
            (z : Agent n (chainLength P ε) → Chore n (chainLength P ε) → ℝ)
            (v : Fin n → ℚ),
            (completedMarket P ε).IsCE p z ∧
            (fun i => (v i : ℝ)) = decoder (tParam P ε) p ∧
            encVector v = g (pairCode I y) := by sorry

end LinearChoresCLS
