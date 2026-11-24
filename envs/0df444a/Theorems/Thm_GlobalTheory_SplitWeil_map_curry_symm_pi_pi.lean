-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_map_curry_symm_pi_pi
-- name    : GlobalTheory.SplitWeil.map_curry_symm_pi_pi
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:21:06.436804+00:00
-- url     : https://prove2.me/theorems/6449c39e-bba2-404e-9380-c458b2b2aad8
-- title:
--   Split Weil: map curry symm pi pi
-- statement:
--   The Split Weil construction uses the map curry symm pi pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LinearChangeOfVariablesLocalFieldMatrix.lean#L10-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LinearChangeOfVariablesLocalFieldMatrix.lean#L10-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker
open GlobalTheory GlobalTheory.SplitWeil

theorem GlobalTheory.SplitWeil.map_curry_symm_pi_pi {X a b : Type} [MeasurableSpace X] [Fintype a] [Fintype b] (ν : Measure X)
    [SigmaFinite ν] :
    Measure.map (MeasurableEquiv.curry b a X).symm (Measure.pi fun _ : b => Measure.pi fun _ : a => ν) =
      Measure.pi fun _ : b × a => ν := by sorry
