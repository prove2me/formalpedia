-- Prove2me | Theorems.Thm_GlobalTheory_InvBilinTest_isLocallyConstant_cosetInd
-- name    : GlobalTheory.InvBilinTest.isLocallyConstant_cosetInd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:20:16.635305+00:00
-- url     : https://prove2.me/theorems/0c2bafda-b4d3-4851-8cf5-e35c50974aa9
-- title:
--   Inv Bilin Test: is Locally Constant coset Ind
-- statement:
--   The Inv Bilin Test construction uses the is Locally Constant coset Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantCosetInd.lean#L35-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantCosetInd.lean#L35-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantCosetInd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
noncomputable section
open GlobalTheory GlobalTheory.InvBilinTest
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem GlobalTheory.InvBilinTest.isLocallyConstant_cosetInd (K : Subgroup G) (ho : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) : IsLocallyConstant (cosetInd K ho hK) := by sorry
