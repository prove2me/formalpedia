-- Prove2me | Theorems.Thm_LearnThenTest_bonferroni_controls_fwer
-- name    : LearnThenTest.bonferroni_controls_fwer
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T00:10:44.985536+00:00
-- url     : https://prove2.me/theorems/407e777e-341f-416a-8cd6-3ef12cc179ca
-- title:
--   Proposition 2: Bonferroni controls FWER
-- statement:
--   Let $N\ge0$ hypotheses have p-values $p_1,\dots,p_N$ and let $\delta\in(0,1)$. The Bonferroni correction
--
--   $$\mathcal A^{(\mathrm{Bf})}(p_1,\dots,p_N)=\{j: p_j\le\delta/N\}$$
--
--   is an FWER-controlling algorithm at level $\delta$. For every joint law of the p-values on $[0,1]^N$ and every set $J_0$ of true nulls whose p-values are valid, it rejects no true null with probability at least $1-\delta$.
--
--   **Formalization Note** Definition 2's measurability requirement is part of the conclusion. The range $\delta\in(0,1)$ is the paper's range for error levels (the inputs of Algorithms 1 and 2). Some restriction is needed: for $\delta<0$ the requirement "probability at least $1-\delta>1$" cannot be met by any algorithm.
-- source:
--   Angelopoulos, Bates, Candès, Jordan and Lei, Learn then Test: Calibrating Predictive Algorithms to Achieve Risk Control, arXiv:2110.01052v5 (2022), Section 2.3, Proposition 2, p. 4; proof in Appendix C, p. 22

import Mathlib
import Definitions.Def_LearnThenTest_Basic

open MeasureTheory ProbabilityTheory Filter

namespace LearnThenTest

theorem bonferroni_controls_fwer (N : ℕ) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    IsFWERControlling N δ (bonferroni N δ) := by sorry

end LearnThenTest
