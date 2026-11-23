-- Prove2me | Theorems.Thm_GlobalTheory_SW_Hyper_exists_fun
-- name    : GlobalTheory.SW.Hyper.exists_fun
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:20.222955+00:00
-- url     : https://prove2.me/theorems/961e65e1-42d6-4d26-a360-c5f6fe714422
-- title:
--   Hyper: exists fun
-- statement:
--   The Hyper construction uses the exists fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/CycOfPrime.lean#L11-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/CycOfPrime.lean#L11-L45

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

theorem GlobalTheory.SW.Hyper.exists_fun (P : Ideal O) [hP : P.IsMaximal] (N : Submodule O M) (v : M) (hv : v ∉ N)
    (hPv : ∀ c ∈ P, c • v ∈ N) (hc : ∀ x, ∃ r : O, x - r • v ∈ N) :
    ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N := by sorry
