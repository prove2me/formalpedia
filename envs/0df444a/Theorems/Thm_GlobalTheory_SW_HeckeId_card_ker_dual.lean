-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeckeId_card_ker_dual
-- name    : GlobalTheory.SW.HeckeId.card_ker_dual
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:41:55.003302+00:00
-- url     : https://prove2.me/theorems/d7f91ea8-72f0-47c5-bfd0-3cbce77a904f
-- title:
--   Hecke Id: card ker dual
-- statement:
--   The Hecke Id construction uses the card ker dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeckeRelationAdmissibleFamilyPointwise.lean#L27-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId

theorem GlobalTheory.SW.HeckeId.card_ker_dual (F V W : Type) [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] [FiniteDimensional F V] [FiniteDimensional F W] (g : V →ₗ[F] W) :
    Nat.card (LinearMap.ker g) * Nat.card F ^ Module.finrank F W =
      Nat.card (LinearMap.ker g.dualMap) * Nat.card F ^ Module.finrank F V := by sorry
