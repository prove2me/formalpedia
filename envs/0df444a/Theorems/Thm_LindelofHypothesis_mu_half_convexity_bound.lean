-- Prove2me | Theorems.Thm_LindelofHypothesis_mu_half_convexity_bound
-- name    : LindelofHypothesis.mu_half_convexity_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T16:41:37.255096+00:00
-- url     : https://prove2.me/theorems/a671b575-140e-4079-ba48-cda4a976c54e
-- title:
--   Convexity bound: $0\le\mu(\tfrac12)\le\tfrac14$ (Lindelöf 1908)
-- statement:
--   The growth exponent on the critical line satisfies
--   $$0\le\mu\!\left(\tfrac12\right)\le\tfrac14 ,$$
--   where $\mu(\sigma)=\inf\{a\in\mathbb R:\zeta(\sigma+iT)=O(T^{a})\}$. In particular $\zeta(\tfrac12+it)=O(t^{1/4+\varepsilon})$ for every $\varepsilon>0$.
--
--   This is Lindelöf's convexity bound (1908), the first entry of the table of known bounds for $\mu(\tfrac12)$.
--
--   **Formalization Note** $\mu$ is `LindelofHypothesis.mu`, valued in the extended reals.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "The μ function", sentence "... implies that 0 ≤ μ(1/2) ≤ 1/4", and first row of the table (Lindelöf 1908, convexity bound).

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem mu_half_convexity_bound : 0 ≤ mu (1 / 2) ∧ mu (1 / 2) ≤ ((1 / 4 : ℝ) : EReal) := by sorry

end LindelofHypothesis
