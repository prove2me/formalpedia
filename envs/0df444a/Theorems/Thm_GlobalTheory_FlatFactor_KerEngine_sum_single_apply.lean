-- Prove2me | Theorems.Thm_GlobalTheory_FlatFactor_KerEngine_sum_single_apply
-- name    : GlobalTheory.FlatFactor.KerEngine.sum_single_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:38:00.509585+00:00
-- url     : https://prove2.me/theorems/844306ac-6bb1-4662-aa64-0dcd6e9ce810
-- title:
--   Ker Engine: sum single apply
-- statement:
--   The Ker Engine construction uses the sum single apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LinearMapKillsPartialEvalIntegralKernelOfLaws.lean#L82-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LinearMapKillsPartialEvalIntegralKernelOfLaws.lean#L82-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatLinearFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillsPartialEvalIntegralKernelOfLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.KerEngine
open GlobalTheory.FlatFactor
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

theorem GlobalTheory.FlatFactor.KerEngine.sum_single_apply (it : Finset (m × m')) (a : m × m' → k) (r : m) (q : m') :
    (∑ e ∈ it, Matrix.single e.1 e.2 (a e)) r q = if (r, q) ∈ it then a (r, q) else 0 := by sorry
