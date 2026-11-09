-- Prove2me | Theorems.Thm_MaoLowDegree_Counterexample_lemma_3_5
-- name    : MaoLowDegree.Counterexample.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:40.697115+00:00
-- url     : https://prove2.me/theorems/6a79027f-2e07-4dc9-99d1-7badde6220e8
-- title:
--   Lemma 3.5 — simultaneous choice of constants
-- statement:
--   Let $\gamma_0>0$ be a puncturing constant as in Lemma 3.1. For every fixed integer $r\ge3$ and real constant $b>0$, there exist positive rational $a,\sigma$ and $\varepsilon_0\in(0,1)$ such that
--   $$a>2,\quad \frac\sigma a<\min\{\gamma_0,\tfrac12\},\quad \tfrac12<ah_2(\sigma/a)<1,$$
--   and, for every $\varepsilon\in[0,\varepsilon_0]$, with $\lambda=-\log_2(1-\varepsilon)$,
--   $$\frac{r\sigma}{b}<\tfrac12,\qquad bh_2(r\sigma/b)<\tfrac12-a\lambda.$$
--
--   These are all hypotheses of both rank bounds simultaneously. Rationality of the constants permits a fixed finite program; none depends on $n$ or on the eventual chosen noise rate.
--
--   Differences from the source:
--   - encoding: the positive constant gamma0 supplied by Lemma 3.1 → a positive gamma0 with its Puncturing property explicitly supplied; reason: keeps the referenced constant separate from its unproved theorem statement
--   - encoding: the hypotheses of Lemmas 3.3 and 3.4 → NullConditions and PlantedConditions expanded as the displayed inequalities; reason: retains every inequality and both rational positivity conditions
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), Lemma 3.5, p.14

import Definitions.Def_MaoLowDegree_Counterexample_computationalClaims

open Classical Filter
open scoped Topology
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- Lemma 3.5, p.14. γ₀ is the positive constant supplied by Lemma 3.1. -/
theorem lemma_3_5 (γ₀ : ℝ) (hγ : 0 < γ₀) (hpunct : Puncturing γ₀)
    (r : ℕ) (hr : 3 ≤ r) (b : ℝ) (hb : 0 < b) :
    ∃ a σ : ℚ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      NullConditions γ₀ a σ ∧ (a : ℝ) * binaryEntropy ((σ : ℝ) / a) < 1 ∧
      ∀ ε : Rate, ε.val ≤ ε₀ → PlantedConditions r b a σ ε := by sorry

end MaoLowDegree.Counterexample
