-- Prove2me | Theorems.Thm_MaoLowDegree_Counterexample_lemma_2_1
-- name    : MaoLowDegree.Counterexample.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:29.411194+00:00
-- url     : https://prove2.me/theorems/bcbfd5b0-2b8f-4348-8a1d-7da80748ece3
-- title:
--   Lemma 2.1 — random polynomial bias tail
-- statement:
--   There are positive absolute constants $\beta_1,\beta_2$ and an absolute integer threshold $m_0$ such that for every $m\ge m_0$ and every integer $1\le r\le m/2$, a polynomial $f\in\mathrm{RM}(m,r)$ with independent uniform binary multilinear coefficients satisfies
--   $$\Pr_f\{|\operatorname{bias}(f)|>2^{-\beta_1m/r}\}\le 2^{-\beta_2\sum_{j=0}^r\binom mj}.$$
--
--   This is the result quoted as [BEHL12, Lemma 1.2]. It supplies the bias-tail constants for selecting a large low-bias subspace; it is a theorem to prove, not an axiom. The constants and threshold are uniform over the full displayed range of $r$.
--
--   Differences from the source:
--   - encoding: uniform multilinear polynomial in RM(m,r) → pushforward of the uniform vector of all coefficients; reason: all allowed monomial coefficients are independent fair binary elements
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), Lemma 2.1 [BEHL12, Lemma 1.2], p.8

import Definitions.Def_MaoLowDegree_Counterexample_computationalClaims

open Classical Filter
open scoped Topology
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- Lemma 2.1 [BEHL12, Lemma 1.2], p.8. Absolute constants precede all m and r. -/
theorem lemma_2_1 :
    ∃ β₁ β₂ : ℝ, 0 < β₁ ∧ 0 < β₂ ∧ BiasTail β₁ β₂ := by sorry

end MaoLowDegree.Counterexample
