-- Prove2me | Theorems.Thm_GlobalTheory_FullFlag_ofBasis_eq_ofBasis_iff
-- name    : GlobalTheory.FullFlag.ofBasis_eq_ofBasis_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:40:14.303796+00:00
-- url     : https://prove2.me/theorems/eb205b8d-8a35-4cba-851a-861ee86fc4a3
-- title:
--   Full Flag: of Basis eq of Basis iff
-- statement:
--   The Full Flag construction uses the of Basis eq of Basis iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L254-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsAdaptedOfIsLocalRing.lean#L254-L259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.FullFlag
variable {n : ℕ}

theorem GlobalTheory.FullFlag.ofBasis_eq_ofBasis_iff (b b' : Basis (Fin n) R M) :
    ofBasis b' = ofBasis b ↔ ∃ g ∈ upperTriangularGL (Fin n) R, basisMulGL b g = b' := by sorry
