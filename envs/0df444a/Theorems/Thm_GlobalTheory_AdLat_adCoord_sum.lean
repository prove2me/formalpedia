-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_adCoord_sum
-- name    : GlobalTheory.AdLat.adCoord_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:42.824701+00:00
-- url     : https://prove2.me/theorems/2a1fbf8b-e654-44aa-9d3e-d0947df40019
-- title:
--   Ad Lat: ad Coord sum
-- statement:
--   The Ad Lat construction uses the ad Coord sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MemAdelicCompletionPseudoBasisIff.lean#L52-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MemAdelicCompletionPseudoBasisIff.lean#L52-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdLat
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem GlobalTheory.AdLat.adCoord_sum (e : Module.Basis (Fin n) E (Fin n → E))
    (z : Fin n → _root_.GlobalTheory.AdLat.RA F E) (b : Fin n) :
    _root_.GlobalTheory.AdLat.adCoord F e b (∑ a, z a • _root_.GlobalTheory.AdLat.fv F (e a)) = z b := by sorry
