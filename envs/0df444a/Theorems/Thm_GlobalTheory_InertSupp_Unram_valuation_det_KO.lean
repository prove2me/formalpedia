-- Prove2me | Theorems.Thm_GlobalTheory_InertSupp_Unram_valuation_det_KO
-- name    : GlobalTheory.InertSupp.Unram.valuation_det_KO
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:19.63134+00:00
-- url     : https://prove2.me/theorems/fd0e2028-92dc-59a3-a3cd-13ebcb2b44b8
-- title:
--   Unram: valuation det KO
-- statement:
--   The Unram construction uses the valuation det KO property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NoUnramTwistOfNoInert.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NoUnramTwistOfNoInert.lean#L17-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NoUnramTwistOfNoInert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory GlobalTheory.InertSupp GlobalTheory.InertSupp.Unram
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open ValuativeRel Matrix MeasureTheory
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.InertSupp.Unram.valuation_det_KO {m : Type} [Fintype m] [DecidableEq m] {g : GL m k}
    (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k m) :
    valuation k (GeneralLinearGroup.det g : k) = 1 := by sorry
