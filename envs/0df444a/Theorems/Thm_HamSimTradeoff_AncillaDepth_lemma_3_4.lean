-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_lemma_3_4
-- name    : HamSimTradeoff.AncillaDepth.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:13.926378+00:00
-- url     : https://prove2.me/theorems/93ad564a-79ff-4c61-8c4b-4e4e452912be
-- title:
--   Lemma 3.4 — Markov-type inequality for complex exponential sums
-- statement:
--   There is an absolute constant $C>1$ such that for every integer $M\ge0$, every $b,a_1,\ldots,a_M\in\mathbb C$, and every list of distinct real frequencies $\lambda_1,\ldots,\lambda_M$, the function $f(t)=bt+\sum_{j=1}^M a_je^{i\lambda_jt}$ obeys
--   $$\|f'\|_{[0,1]}\le C\left(108(M+2)^5+\sum_{j=1}^M\lambda_j^2\right)^{1/2}\|f\|_{[0,1]}.$$
--   Both norms are the supremum of the complex modulus on the whole closed interval. The square root covers the entire bracket. This is the source's cited exponential-sum estimate, including its footnote extension allowing a nonzero linear term.
--
--   **Formalization Note** The paper's constant $C>1$ is absolute and is chosen before every frequency and coefficient. The sum can be empty; no frequency lower bound or separation assumption is added.
--
--   Differences from the source:
--   - encoding: an unspecified absolute constant C>1 → ∃ C>1 before M, b, a and λ; reason: this makes the uniform constant dependence explicit
--   - encoding: L∞ norm on the stated closed interval → sSup of the pointwise complex moduli on that interval; reason: the functions and their iterated derivatives are continuous, so the nonempty compact interval has a finite maximum
--   - reading: coefficients b, a_j of unstated type → b, a_j ∈ ℂ; reason: the lemma is applied to the complex-valued g(t) (p.19), so the complex reading is the one the proof needs and contains the real case
-- source:
--   Yuxin Zhang, Changpeng Shao, Time-space tradeoffs for Hamiltonian simulation, STOC 2027 submission #334 (October 2026), p.17, Lemma 3.4, Eq. (3.7), and footnote 10 (citing Erdélyi 2017, Theorem 9.1)

import Definitions.Def_HamSimTradeoff_AncillaDepth_Response
import Definitions.Def_HamSimTradeoff_AncillaDepth_ExponentialSums
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth

/-- Erdélyi's Markov-type inequality, including the source's linear-term extension. -/
theorem lemma_3_4 :
    ∃ C : ℝ, 1 < C ∧ ∀ (M : ℕ) (b : ℂ) (a : Fin M → ℂ) (freq : Fin M → ℝ),
      Function.Injective freq →
      intervalNorm (deriv (exponentialSum b a freq)) 0 1 ≤
        C * Real.sqrt (108 * ((M : ℝ) + 2) ^ 5 + ∑ j, freq j ^ 2) *
          intervalNorm (exponentialSum b a freq) 0 1 := by sorry

end HamSimTradeoff.AncillaDepth
