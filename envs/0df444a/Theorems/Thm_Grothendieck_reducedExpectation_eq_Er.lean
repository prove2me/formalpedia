-- Prove2me | Theorems.Thm_Grothendieck_reducedExpectation_eq_Er
-- name    : Grothendieck.reducedExpectation_eq_Er
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T05:56:54.996174+00:00
-- url     : https://prove2.me/theorems/0014a754-7f0d-4ced-9c7b-a2bde0691328
-- title:
--   Lemma 2.1's canonical identity for $r\ge2$: the rounding expectation is $E_r(\tau)$
-- statement:
--   Let $W$ be a random $r\times2$ matrix whose $r$ rows are independent centred bivariate Gaussians of correlation $\tau$, and let `reducedIntegrand` be the cosine of the angle between its two columns. For $r\ge2$ and $|\tau|<1$,
--   $$\int_W \mathrm{reducedIntegrand}_r(W)\,d(\texttt{reducedLaw}\,r\,\tau)=E_r(\tau),$$
--   where $E_r$ is the series of the paper's Lemma 2.1,
--   $$E_r(t)=\frac{\Gamma(\frac{r+1}{2})}{\sqrt\pi\,\Gamma(\frac r2)}\,t\int_0^1\frac{x^{-1/2}(1-x)^{\frac{r-1}{2}}}{\sqrt{1-t^2x}}\,dx .$$
--   This is the matrix Grothendieck identity evaluated on the canonical two-column law: the expectation of the rounded cosine equals the value the paper computes for $E_r$. Its proof composes the published chain — the Laplace/Fubini reduction, the substitutions $s=u^2/2$, $t=v^2/2$, the $p$-integral, the substitution $x=q^2/(1+q^2)$ — with the Gamma bookkeeping $\Gamma(\frac{r+2}{2})=\frac r2\Gamma(\frac r2)$ that reconciles the constants.
--
--   Only the case $r\ge2$ is covered here: rank $1$ is the classical arcsine law and is a separate node, and the endpoint $|\tau|=1$ needs its own argument.
--
--   **Formalization Note** One of the two remaining inputs to the paper's matrix Grothendieck identity.
-- source:
--   Briet, de Oliveira Filho, Vallentin, Theory of Computing 10(4), 2014, pp. 77-105 - Lemma 2.1, equation (2.1), evaluated on the canonical two-column law.

import Mathlib
import Definitions.Def_Grothendieck_Reduced
import Definitions.Def_Grothendieck_Series

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **Lemma 2.1's canonical identity, for `r ≥ 2`.** The rounding expectation equals the paper's
series `E_r` at the correlation `τ`. -/
theorem reducedExpectation_eq_Er (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ)) = Er r τ := by sorry

end Grothendieck
