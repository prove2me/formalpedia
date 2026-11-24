-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriInj_exists_wall
-- name    : GlobalTheory.IwahoriInj.exists_wall
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:24:20.183561+00:00
-- url     : https://prove2.me/theorems/d25cbeab-5a58-45f4-92ad-e50a2e73a3b8
-- title:
--   Iwahori Inj: exists wall
-- statement:
--   The Iwahori Inj construction uses the exists wall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L169-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L169-L203

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
variable {n : Type}

theorem GlobalTheory.IwahoriInj.exists_wall [Fintype n] {f F : n → n → ℤ} (hf : Chamber f) (hF : Chamber F) (hne : f ≠ F) :
    ∃ i j, i ≠ j ∧ f j i < F j i ∧ ∀ l, l ≠ i → l ≠ j → f j i < f j l + f l i := by sorry
