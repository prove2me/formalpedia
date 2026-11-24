-- Prove2me | Theorems.Thm_GlobalTheory_CMFormBound_conj_sqrt
-- name    : GlobalTheory.CMFormBound.conj_sqrt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:03:12.443058+00:00
-- url     : https://prove2.me/theorems/dcc8406c-f74e-4c9b-b318-a49f034eb5ef
-- title:
--   CMForm Bound: conj sqrt
-- statement:
--   The CMForm Bound construction uses the conj sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodGaloisIntegral.lean#L58-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodGaloisIntegral.lean#L58-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CMFormBound

theorem GlobalTheory.CMFormBound.conj_sqrt (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ) (hd : d.Prime) (r : E)
    (hr : r ^ 2 = -(d : E)) : IsCMField.complexConj E r = -r := by sorry
