-- Prove2me | Theorems.Thm_LindelofHypothesis_mu_eq_zero_of_one_lt
-- name    : LindelofHypothesis.mu_eq_zero_of_one_lt
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T16:35:55.420237+00:00
-- url     : https://prove2.me/theorems/552870a9-e9e2-480f-85f3-707f70acb408
-- title:
--   $\mu(\sigma)=0$ for $\sigma>1$
-- statement:
--   Let $\mu(\sigma)=\inf\{a\in\mathbb R:\zeta(\sigma+iT)=O(T^{a})\}$. For every real $\sigma>1$,
--   $$\mu(\sigma)=0 .$$
--
--   This is the value of the growth exponent in the half-plane of absolute convergence; it is one of the three properties of $\mu$ from which the source derives the shape of $\mu$ under the Lindelöf hypothesis.
--
--   **Formalization Note** $\mu$ is `LindelofHypothesis.mu`, valued in the extended reals.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "The μ function", sentence "It is trivial to check that μ(σ) = 0 for σ > 1".

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem mu_eq_zero_of_one_lt (σ : ℝ) (hσ : 1 < σ) : mu σ = 0 := by sorry

end LindelofHypothesis
