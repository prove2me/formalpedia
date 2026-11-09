-- Prove2me | Theorems.Thm_MaoLowDegree_Counterexample_lemma_2_2
-- name    : MaoLowDegree.Counterexample.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:24.685972+00:00
-- url     : https://prove2.me/theorems/2b2094b6-06d5-482d-8a6f-d662715a8776
-- title:
--   Lemma 2.2 — low-bias subspace
-- statement:
--   Fix $r,\beta_1,\beta_2,b,\kappa$ satisfying the numerical setup on p.8, with $\beta_1,\beta_2$ having the bias-tail property of Lemma 2.1. Set $m=\lceil b\ell_n\rceil$, $R=\sum_{j=0}^r\binom mj$, $K=\lfloor\kappa R\rfloor$ and $\eta=2^{-\beta_1m/r}$. For all sufficiently large $n$ there exists a subspace $W\le\mathrm{RM}(m,r)$ such that
--   $$\dim_{\mathbb F_2}W=K,\qquad |\operatorname{bias}(f)|\le\eta\quad(0\ne f\in W).$$
--
--   This provides the actual subspace used by the subsequent evaluation construction. Its dimension and low bias are conclusions, rather than properties included in the definition of RM.
--
--   Differences from the source:
--   - encoding: the bias-tail constants from Lemma 2.1 and the fixed numerical setup on p.8 → explicit BiasTail and Admissible hypotheses; reason: expands the preceding parameter choices while keeping dimension and low bias in the conclusion
--   - encoding: for all sufficiently large n and probability 1-o(1) → Filter.atTop eventual assertions and Tendsto to 1; reason: these are the literal asymptotic quantifiers, with all fixed parameters before n
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), Lemma 2.2 and its standing parameter setup, p.8

import Definitions.Def_MaoLowDegree_Counterexample_computationalClaims

open Classical Filter
open scoped Topology
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- Lemma 2.2, p.8, with the numerical setup and the bias-tail constants from Lemma 2.1. -/
theorem lemma_2_2 (r : ℕ) (β₁ β₂ b κ : ℝ)
    (hparams : Admissible r β₁ β₂ b κ) (htail : BiasTail β₁ β₂) :
    ∀ᶠ n : ℕ in atTop, ∃ W : Submodule F₂ (Vec (ambientDimension b n) → F₂),
      W ≤ RM (ambientDimension b n) r ∧
      Module.finrank F₂ W = codeDimension r b κ n ∧
      LowBias W (eta r β₁ b n) := by sorry

end MaoLowDegree.Counterexample
