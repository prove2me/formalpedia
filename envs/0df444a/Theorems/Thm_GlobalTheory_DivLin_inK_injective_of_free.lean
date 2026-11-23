-- Prove2me | Theorems.Thm_GlobalTheory_DivLin_inK_injective_of_free
-- name    : GlobalTheory.DivLin.inK_injective_of_free
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:04.175414+00:00
-- url     : https://prove2.me/theorems/08c4b62d-36b4-47d7-9cd7-1dcefa3e6414
-- title:
--   Div Lin: in K injective of free
-- statement:
--   The Div Lin construction uses the in K injective of free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L8-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L8-L17

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

theorem GlobalTheory.DivLin.inK_injective_of_free {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K] (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] :
    Function.Injective (inK (O := O) K H) := by sorry
