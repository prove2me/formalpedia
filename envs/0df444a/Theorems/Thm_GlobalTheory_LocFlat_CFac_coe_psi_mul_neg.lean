-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_CFac_coe_psi_mul_neg
-- name    : GlobalTheory.LocFlat.CFac.coe_psi_mul_neg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:02.415239+00:00
-- url     : https://prove2.me/theorems/9b16c5f9-e15d-4d09-8fac-dfce70724857
-- title:
--   CFac: coe psi mul neg
-- statement:
--   The CFac construction uses the coe psi mul neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HeisenbergInvariantFactorsContraction.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HeisenbergInvariantFactorsContraction.lean#L14-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLinearOfBilinearSchwartzBruhatProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeisenbergInvariantFactorsContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.CFac

theorem GlobalTheory.LocFlat.CFac.coe_psi_mul_neg {k : Type} [AddGroup k] (ψ : AddChar k Circle) (a : k) : (ψ a : ℂ) * ψ (-a) = 1 := by sorry
