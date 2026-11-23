-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_aut_eq_one_or_of_finrank_two
-- name    : GlobalTheory.AdLat.aut_eq_one_or_of_finrank_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:13.676822+00:00
-- url     : https://prove2.me/theorems/cbda6428-5594-418e-9ff8-d01a14d924e6
-- title:
--   Ad Lat: aut eq one or of finrank two
-- statement:
--   The Ad Lat construction uses the aut eq one or of finrank two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/Hilbert90AdeleRingTensorQuadratic.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/Hilbert90AdeleRingTensorQuadratic.lean#L37-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIdempotentIsUnitOneAddOrSubAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_Hilbert90AdeleRingTensorQuadratic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat

theorem GlobalTheory.AdLat.aut_eq_one_or_of_finrank_two {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (g : E ≃ₐ[F] E) : g = 1 ∨ g = c := by sorry
