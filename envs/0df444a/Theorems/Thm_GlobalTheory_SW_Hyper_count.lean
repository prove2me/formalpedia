-- Prove2me | Theorems.Thm_GlobalTheory_SW_Hyper_count
-- name    : GlobalTheory.SW.Hyper.count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:45.222471+00:00
-- url     : https://prove2.me/theorems/d5200302-1edd-47fc-b1d2-d0e47d0b24c4
-- title:
--   Hyper: count
-- statement:
--   The Hyper construction uses the count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/CycOfPrime.lean#L120-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/CycOfPrime.lean#L120-L178

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
attribute [local instance] Ideal.Quotient.field

theorem GlobalTheory.SW.Hyper.count [IsDomain O] [Module.Finite O M] [Module.Projective O M] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] :
    {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}.Finite ∧
    {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}.ncard *
      (Nat.card (O ⧸ P) - 1) = Nat.card (O ⧸ P) ^ Module.finrank O M - 1 := by sorry
