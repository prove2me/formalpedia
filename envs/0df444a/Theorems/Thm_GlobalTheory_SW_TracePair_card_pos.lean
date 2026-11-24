-- Prove2me | Theorems.Thm_GlobalTheory_SW_TracePair_card_pos
-- name    : GlobalTheory.SW.TracePair.card_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:33.627262+00:00
-- url     : https://prove2.me/theorems/fe156178-ef44-4485-b951-081a9ad4981f
-- title:
--   Trace Pair: card pos
-- statement:
--   The Trace Pair construction uses the card pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TracePairingGeDetImPowHermitianHalfSpace.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TracePairingGeDetImPowHermitianHalfSpace.lean#L12-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TracePairingGeDetImPowHermitianHalfSpace
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TracePair
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.SW.TracePair.card_pos {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) : 0 < Ψ.card := by sorry
