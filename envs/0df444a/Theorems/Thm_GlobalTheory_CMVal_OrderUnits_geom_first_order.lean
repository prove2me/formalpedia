-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_OrderUnits_geom_first_order
-- name    : GlobalTheory.CMVal.OrderUnits.geom_first_order
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:05:11.156629+00:00
-- url     : https://prove2.me/theorems/414934bb-ee89-4bc4-bffb-cc1e66022d0d
-- title:
--   Order Units: geom first order
-- statement:
--   The Order Units construction uses the geom first order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmRingClassOrderUnitsEqMaxRealSubfieldUnits.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmRingClassOrderUnitsEqMaxRealSubfieldUnits.lean#L46-L55

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits

theorem GlobalTheory.CMVal.OrderUnits.geom_first_order {R : Type} [CommRing R] (t : R) (n : ℕ) :
    ∃ r, ∑ i ∈ Finset.range n, (1 + t) ^ i = n + (n.choose 2 : ℕ) * t + t ^ 2 * r := by sorry
