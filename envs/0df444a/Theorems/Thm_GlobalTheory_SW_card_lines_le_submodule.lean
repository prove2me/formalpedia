-- Prove2me | Theorems.Thm_GlobalTheory_SW_card_lines_le_submodule
-- name    : GlobalTheory.SW.card_lines_le_submodule
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:09.023598+00:00
-- url     : https://prove2.me/theorems/eff514f6-f7a8-4259-ac01-16108822fde4
-- title:
--   SW: card lines le submodule
-- statement:
--   The SW construction uses the card lines le submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/CardKerMatrixFiniteField.lean#L11-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/CardKerMatrixFiniteField.lean#L11-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW

theorem GlobalTheory.SW.card_lines_le_submodule (F V : Type) [Field F] [AddCommGroup V] [Module F V] [Finite V]
    (K : Submodule F V) :
    Nat.card {l : Submodule F V // Module.finrank F l = 1 ∧ l ≤ K} * (Nat.card F - 1) + 1
      = Nat.card K := by sorry
