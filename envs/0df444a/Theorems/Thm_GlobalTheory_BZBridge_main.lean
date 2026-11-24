-- Prove2me | Theorems.Thm_GlobalTheory_BZBridge_main
-- name    : GlobalTheory.BZBridge.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:36:20.133954+00:00
-- url     : https://prove2.me/theorems/07e01c3a-62a9-4451-8505-8fac24a66ce8
-- title:
--   BZBridge: main
-- statement:
--   The BZBridge construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleAdmissible.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleAdmissible.lean#L83-L87

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLengthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLengthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleAdmissible
import Theorems.Thm_GlobalTheory_PowerTwoNormLowerBound_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.BZBridge

theorem GlobalTheory.BZBridge.main : GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength →
    GlobalTheory.Published.BernsteinZelevinskyFiniteness := by sorry
