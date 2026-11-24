-- Prove2me | Theorems.Thm_GlobalTheory_DivLin_restr_mul_eq_zero
-- name    : GlobalTheory.DivLin.restr_mul_eq_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:50:35.121526+00:00
-- url     : https://prove2.me/theorems/6534195f-4d4e-46a4-ba23-464290368ff1
-- title:
--   Div Lin: restr mul eq zero
-- statement:
--   The Div Lin construction uses the restr mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L33-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms
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
open GlobalTheory GlobalTheory.DivLin
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
  {H : Type} [AddCommGroup H] [Module O H]
variable [Module.Free O H]

theorem GlobalTheory.DivLin.restr_mul_eq_zero {D : O} {N N' : Module.End K (K ⊗[O] H)} {M M' : Module.End O H}
    (hM : IsScaledRestr D N M) (hM' : IsScaledRestr D N' M') (h : N * N' = 0) : M * M' = 0 := by sorry
