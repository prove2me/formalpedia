-- Prove2me | Theorems.Thm_GlobalTheory_DivLin_inK_apply_end
-- name    : GlobalTheory.DivLin.inK_apply_end
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:50:51.218437+00:00
-- url     : https://prove2.me/theorems/0f4ebb1b-bf0f-4bae-b9e5-e0a80a7f6ea0
-- title:
--   Div Lin: in K apply end
-- statement:
--   The Div Lin construction uses the in K apply end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L28-L29

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

theorem GlobalTheory.DivLin.inK_apply_end (f : Module.End O H) (h : H) : inK K H (f h) = f.baseChange K (inK K H h) := by sorry
