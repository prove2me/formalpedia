-- Prove2me | Theorems.Thm_LindelofHypothesis_mu_functional_equation
-- name    : LindelofHypothesis.mu_functional_equation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:37:02.559965+00:00
-- url     : https://prove2.me/theorems/e15e5880-7975-448f-9a15-4b6156f058c3
-- title:
--   Functional equation for $\mu$: $\mu(\sigma)=\mu(1-\sigma)-\sigma+\tfrac12$
-- statement:
--   For every real $\sigma$,
--   $$\mu(\sigma)=\mu(1-\sigma)-\sigma+\tfrac12 ,$$
--   where $\mu(\sigma)=\inf\{a\in\mathbb R:\zeta(\sigma+iT)=O(T^{a})\}$ (as an extended real number).
--
--   This reflects the functional equation of $\zeta$ to the growth exponent; together with $\mu(\sigma)=0$ for $\sigma>1$ and convexity it determines $\mu$ outside the critical strip.
--
--   **Formalization Note** $\mu$ is `LindelofHypothesis.mu`, valued in the extended reals. The identity is stated in the extended reals; $-\sigma+\tfrac12$ is a finite real shift.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "The μ function", sentence "the functional equation of the zeta function implies that μ(σ) = μ(1 − σ) − σ + 1/2".

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem mu_functional_equation (σ : ℝ) : mu σ = mu (1 - σ) + ((1 / 2 - σ : ℝ) : EReal) := by sorry

end LindelofHypothesis
