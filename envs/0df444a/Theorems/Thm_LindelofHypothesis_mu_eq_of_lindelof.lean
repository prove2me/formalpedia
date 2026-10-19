-- Prove2me | Theorems.Thm_LindelofHypothesis_mu_eq_of_lindelof
-- name    : LindelofHypothesis.mu_eq_of_lindelof
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T16:44:58.42563+00:00
-- url     : https://prove2.me/theorems/620f5fd9-ab66-488c-af78-96585b2371eb
-- title:
--   Under Lindelöf: $\mu(\sigma)=\max(0,\tfrac12-\sigma)$
-- statement:
--   Assume the Lindelöf hypothesis. Then for every real $\sigma$,
--   $$\mu(\sigma)=\begin{cases}0,&\sigma\ge\tfrac12,\\[2pt] \tfrac12-\sigma,&\sigma\le\tfrac12,\end{cases}$$
--   where $\mu(\sigma)=\inf\{a\in\mathbb R:\zeta(\sigma+iT)=O(T^{a})\}$.
--
--   This is the complete shape of the growth exponent predicted by the Lindelöf hypothesis.
--
--   **Formalization Note** `RiemannVonMangoldt.LindelofHypothesis` is the published definition: for every $\varepsilon>0$, $\zeta(\tfrac12+it)=O(t^{\varepsilon})$ as $t\to+\infty$. $\mu$ is `LindelofHypothesis.mu`, valued in the extended reals.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "The μ function", sentence "... implies that μ(σ) is 0 for σ ≥ 1/2 and 1/2 − σ for σ ≤ 1/2".

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem mu_eq_of_lindelof (hL : RiemannVonMangoldt.LindelofHypothesis) (σ : ℝ) :
    mu σ = ((max 0 (1 / 2 - σ) : ℝ) : EReal) := by sorry

end LindelofHypothesis
