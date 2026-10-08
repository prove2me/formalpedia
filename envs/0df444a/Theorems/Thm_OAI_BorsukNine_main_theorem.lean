-- Prove2me | Theorems.Thm_OAI_BorsukNine_main_theorem
-- name    : OAI.BorsukNine.main_theorem
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:23.796228+00:00
-- url     : https://prove2.me/theorems/9b05ba32-6098-4e4e-89ba-f9908ecf987e
-- statement:
--   The theorem states that, in the setting of 4-by-4 real matrices viewed as the Euclidean space of functions on pairs of indices (so they carry the Frobenius-type Euclidean distance), the set of rank-one projector matrices P(u), with entries u_i u_j for unit vectors u in R^4, has four properties. It is compact; it is contained in the set of symmetric 4-by-4 matrices with trace 1; its diameter equals √2; and it is not possible to cover it by ten sets C_0,...,C_9, each contained in the projector set, each of diameter strictly less than √2. In other words, the statement asserts that the projector set cannot be split into ten pieces of smaller diameter. The theorem is admitted in the source (proof left as sorry).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BorsukNine.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BorsukNine.lean; bytes 619..800
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BorsukNine

namespace OAI

namespace BorsukNine

theorem main_theorem :
    IsCompact projectorSet ∧
    projectorSet ⊆ traceOneSymmetric ∧
    Metric.diam projectorSet = Real.sqrt 2 ∧
    ¬ HasTenSmallCover := by
  sorry

end BorsukNine
end OAI
