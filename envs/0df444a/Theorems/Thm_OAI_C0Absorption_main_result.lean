-- Prove2me | Theorems.Thm_OAI_C0Absorption_main_result
-- name    : OAI.C0Absorption.main_result
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:25.046705+00:00
-- url     : https://prove2.me/theorems/464b9a58-35b8-4983-86cf-6b0971a902b6
-- statement:
--   The theorem states that there exists a real normed space Z, in a fixed universe, with the following properties, where C₀ denotes the real Banach space of sequences ℝ-valued on ℕ that tend to zero at infinity, and a map f between metric spaces is bi-Lipschitz if there are constants 0<c≤C with c·d(x,y) ≤ d(f x,f y) ≤ C·d(x,y) for all x,y. First, Z is complete and separable. Second, Z contains no linear copy of C₀: every continuous linear map T from C₀ to Z fails to satisfy ‖Tx‖ ≥ c‖x‖ for all x for any c>0. Third, there is a surjective bi-Lipschitz map F from the product metric space Z × C₀ onto Z. Fourth, there is a bi-Lipschitz map from C₀ into Z. Fifth, Z is metrically universal for separable metric spaces: every separable metric space M, in the base universe, admits a bi-Lipschitz map into Z. Sixth, Z × C₀ is not linearly homeomorphic to Z, that is, there is no continuous linear equivalence, with continuous inverse, between Z × C₀ and Z.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/C0Absorption.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/C0Absorption.lean; bytes 981..1029
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_C0Absorption

namespace OAI

namespace C0Absorption

open scoped ZeroAtInfty

theorem main_result : MainConclusion := by sorry

end C0Absorption
end OAI
