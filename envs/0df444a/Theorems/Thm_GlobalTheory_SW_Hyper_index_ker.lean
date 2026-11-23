-- Prove2me | Theorems.Thm_GlobalTheory_SW_Hyper_index_ker
-- name    : GlobalTheory.SW.Hyper.index_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:36.112655+00:00
-- url     : https://prove2.me/theorems/86932328-3794-42fc-9b71-5c124323bb9f
-- title:
--   Hyper: index ker
-- statement:
--   The Hyper construction uses the index ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/CycOfPrime.lean#L58-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/CycOfPrime.lean#L58-L68

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

theorem GlobalTheory.SW.Hyper.index_ker (P : Ideal O) [hP : P.IsMaximal] (f : M →ₗ[O] O ⧸ P) (hf : f ≠ 0) :
    (LinearMap.ker f).toAddSubgroup.index = Nat.card (O ⧸ P) := by sorry
