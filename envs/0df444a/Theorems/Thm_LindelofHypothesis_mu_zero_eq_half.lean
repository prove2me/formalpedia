-- Prove2me | Theorems.Thm_LindelofHypothesis_mu_zero_eq_half
-- name    : LindelofHypothesis.mu_zero_eq_half
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:41:11.74948+00:00
-- url     : https://prove2.me/theorems/ab4c3cce-6761-45ac-b2dc-d3add5222617
-- title:
--   $\mu(0)=\tfrac12$
-- statement:
--   On the line $\operatorname{Re}s=0$ the growth exponent equals one half:
--   $$\mu(0)=\tfrac12,$$
--   where $\mu(\sigma)=\inf\{a\in\mathbb R:\zeta(\sigma+iT)=O(T^{a})\}$.
--
--   This is the second boundary value used in Lindelöf's convexity bound.
--
--   **Formalization Note** $\mu$ is `LindelofHypothesis.mu`, valued in the extended reals.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; section "The μ function", sentence "Lindelöf's convexity result together with μ(1) = 0 and μ(0) = 1/2 implies that 0 ≤ μ(1/2) ≤ 1/4".

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis

theorem mu_zero_eq_half : mu 0 = ((1 / 2 : ℝ) : EReal) := by sorry

end LindelofHypothesis
