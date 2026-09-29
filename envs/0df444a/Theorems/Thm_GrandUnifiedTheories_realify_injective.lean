-- Prove2me | Theorems.Thm_GrandUnifiedTheories_realify_injective
-- name    : GrandUnifiedTheories.realify_injective
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:03:30.353285+00:00
-- url     : https://prove2.me/theorems/d4b3dba9-913d-447a-ae3c-aba14a4e79b0
-- title:
--   Realification is injective
-- statement:
--   Realification loses no information: if two complex $5\times5$ matrices have the same realification, they are equal. Formally, $\rho$ is injective:
--
--   $$\rho(A) = \rho(B)\ \Longrightarrow\ A = B .$$
--
--   With multiplicativity and the previous milestone, this is what makes the phrase "$\mathrm{SU}(5)$ is a subgroup of $\mathrm{SO}(10)$" literally true rather than merely a statement about a homomorphic image, and it is what allows the goal theorem to be read as an equality of subgroups of $\mathrm{SO}(10)$.
-- source:
--   John Baez and John Huerta, The Algebra of Grand Unified Theories, https://math.ucr.edu/home/baez/guts.pdf, Section 4, p. 68 (proof of Theorem 8: the identification of SU(5) with a subgroup of SO(10) obtained by forgetting the complex structure)

import Mathlib
import Definitions.Def_GUT_standard_model_group
import Definitions.Def_GUT_realification

namespace GrandUnifiedTheories

theorem realify_injective : Function.Injective realify := by sorry

end GrandUnifiedTheories
