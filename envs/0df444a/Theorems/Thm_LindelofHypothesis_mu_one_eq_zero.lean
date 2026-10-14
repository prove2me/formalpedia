-- Prove2me | Theorems.Thm_LindelofHypothesis_mu_one_eq_zero
-- name    : LindelofHypothesis.mu_one_eq_zero
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:40:39.28374+00:00
-- url     : https://prove2.me/theorems/df6e9959-d9c7-4883-9274-d7df8cf486e7
-- title:
--   $\mu(1)=0$
-- statement:
--   On the line $\operatorname{Re}s=1$ the growth exponent vanishes:
--   $$\mu(1)=0,$$
--   where $\mu(\sigma)=\inf\{a\in\mathbb R:\zeta(\sigma+iT)=O(T^{a})\}$.
--
--   This is one of the two boundary values used in Lindelöf's convexity bound.
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

theorem mu_one_eq_zero : mu 1 = 0 := by sorry

end LindelofHypothesis
