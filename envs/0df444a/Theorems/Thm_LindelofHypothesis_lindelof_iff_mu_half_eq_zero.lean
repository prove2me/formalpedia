-- Prove2me | Theorems.Thm_LindelofHypothesis_lindelof_iff_mu_half_eq_zero
-- name    : LindelofHypothesis.lindelof_iff_mu_half_eq_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T16:44:15.263752+00:00
-- url     : https://prove2.me/theorems/86da457a-ac8a-452c-93af-fffc0888bcf0
-- title:
--   Lindelöf hypothesis $\iff\mu(\tfrac12)=0$
-- statement:
--   The Lindelöf hypothesis holds if and only if
--   $$\mu\!\left(\tfrac12\right)=0 ,$$
--   where $\mu(\sigma)=\inf\{a\in\mathbb R:\zeta(\sigma+iT)=O(T^{a})\}$.
--
--   This is the formulation of the conjecture in terms of the growth exponent used throughout the section on the $\mu$ function and the table of known bounds.
--
--   **Formalization Note** `RiemannVonMangoldt.LindelofHypothesis` is the published definition: for every $\varepsilon>0$, $\zeta(\tfrac12+it)=O(t^{\varepsilon})$ as $t\to+\infty$. $\mu$ is `LindelofHypothesis.mu`, valued in the extended reals.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "The μ function", sentence "The Lindelöf hypothesis states μ(1/2) = 0".

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem lindelof_iff_mu_half_eq_zero : RiemannVonMangoldt.LindelofHypothesis ↔ mu (1 / 2) = 0 := by sorry

end LindelofHypothesis
