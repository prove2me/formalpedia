-- Prove2me | Theorems.Thm_GlobalTheory_SW_Hyper_cyc_of_prime
-- name    : GlobalTheory.SW.Hyper.cyc_of_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:40.636437+00:00
-- url     : https://prove2.me/theorems/ddb15983-c773-48db-b2f7-36478bcc360a
-- title:
--   Hyper: cyc of prime
-- statement:
--   The Hyper construction uses the cyc of prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/CycOfPrime.lean#L70-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/CycOfPrime.lean#L70-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Hyper
variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]

theorem GlobalTheory.SW.Hyper.cyc_of_prime (N : Submodule O M) {q : ℕ} (hq : q.Prime)
    (h : N.toAddSubgroup.index = q) : ∃ v, v ∉ N ∧ ∀ x, ∃ r : O, x - r • v ∈ N := by sorry
