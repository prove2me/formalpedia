-- Prove2me | Theorems.Thm_OnePointComplexity_Dictionary_proposition_2_1
-- name    : OnePointComplexity.Dictionary.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:44.291569+00:00
-- url     : https://prove2.me/theorems/7fce03de-8b1d-474d-b272-2be43f098a5f
-- title:
--   Proposition 2.1 — coefficient interpretation (corrected: degree zero retained)
-- statement:
--   Let $I$ have positive integer element costs and a nonempty family $\mathcal F$ of feasible subsets. Let $A_I(q)$ be its cost polynomial and $\Theta_I(z)=A_I(e^{2\pi iz})$. The order of $A_I$ at $q=0$ and its first nonzero coefficient satisfy
--
--   $$\operatorname{ord}_{q=0} A_I=\mathrm{OPT},\qquad
--   [q^{\operatorname{ord} A_I}]A_I=N_{\mathrm{opt}},\qquad
--   \Theta_I(0)=N_{\mathcal F}.$$
--
--   Moreover, the support of $A_I$ is exactly the set of feasible costs, and for every $k\ge0$,
--
--   $$[q^k]A_I=|\{F\in\mathcal F:c(F)=k\}|.$$
--
--   Thus the exponent spectrum retains the cost multiplicities, not merely existence at a cost. The first coefficient means the coefficient at the least exponent, rather than the highest-degree coefficient.
--
--   Differences from the source:
--   - correction: equation (1) writes the coefficient sum over k≥1 → the cost polynomial and series include k=0 and permit OPT=0; reason: E={e}, c(e)=1, and the feasible family={∅} satisfy every source assumption but give series 1 instead of the printed sum 0; the defining feasible-set sum fixes the intended object
--   - encoding: finite ground elements and order at q=0 → Fin-indexed elements, a natural coefficient polynomial, and natTrailingDegree; reason: the nonempty-family hypothesis makes the polynomial nonzero and the index exactly its least nonzero exponent
-- source:
--   Varsha Gupta, STOC 2027 submission #1733 (October 2026), Proposition 2.1, printed p. 3 (PDF p. 4); equation (1), printed p. 1 (PDF p. 2)

import Definitions.Def_OnePointComplexity_Dictionary_FiniteSeries

set_option autoImplicit false

namespace OnePointComplexity.Dictionary

/-- Proposition 2.1, printed p.3 (PDF 4), with equation (1) corrected at degree zero.
For E={e}, c(e)=1 and F={∅}, the polynomial is 1, not the printed sum over k≥1. -/
theorem proposition_2_1 (I : Instance) (hne : I.feasible.Nonempty) :
    (costPolynomial I).natTrailingDegree = optimum I ∧
    (costPolynomial I).coeff (costPolynomial I).natTrailingDegree = optimalCount I ∧
    theta I 0 = (feasibleCount I : ℂ) ∧
    (costPolynomial I).support = spectrum I ∧
    (∀ k : ℕ, (costPolynomial I).coeff k =
      (I.feasible.filter fun F => setCost I F = k).card) := by sorry

end OnePointComplexity.Dictionary
