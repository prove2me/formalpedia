-- Prove2me | Theorems.Thm_GlobalTheory_DivLin_restr_commute
-- name    : GlobalTheory.DivLin.restr_commute
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:50:10.369784+00:00
-- url     : https://prove2.me/theorems/87733657-0137-432f-a05c-f3e83bf547e6
-- title:
--   Div Lin: restr commute
-- statement:
--   The Div Lin construction uses the restr commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L39-L45

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

theorem GlobalTheory.DivLin.restr_commute {D : O} {N : Module.End K (K ⊗[O] H)} {M : Module.End O H} (f : Module.End O H)
    (hM : IsScaledRestr D N M) (h : Commute N (f.baseChange K)) : Commute M f := by sorry
