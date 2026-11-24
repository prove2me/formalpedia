-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_valuation_map_eq_of_unr
-- name    : GlobalTheory.UnitLemma.Unr.valuation_map_eq_of_unr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:38:06.550361+00:00
-- url     : https://prove2.me/theorems/649c7fdb-67f3-4d21-8102-9429f3fb08c8
-- title:
--   Unr: valuation map eq of unr
-- statement:
--   The Unr construction uses the valuation map eq of unr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegerSpanningFamilyOfUnramifiedExt.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegerSpanningFamilyOfUnramifiedExt.lean#L13-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma IsDedekindDomain IsLocalRing
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

theorem GlobalTheory.UnitLemma.Unr.valuation_map_eq_of_unr (hU : IsUnrExt K K' d φ) (x : K.E) :
    (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) =
      (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x := by sorry
