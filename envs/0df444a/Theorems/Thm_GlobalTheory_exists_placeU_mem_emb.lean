-- Prove2me | Theorems.Thm_GlobalTheory_exists_placeU_mem_emb
-- name    : GlobalTheory.exists_placeU_mem_emb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:51.01933+00:00
-- url     : https://prove2.me/theorems/71bace2e-0af8-4767-a60c-5d82e275aceb
-- title:
--   Global Theory: exists place U mem emb
-- statement:
--   The Global Theory construction uses the exists place U mem emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPrimitiveIdempotentMapEqOne.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPrimitiveIdempotentMapEqOne.lean#L40-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPrimitiveIdempotentMapEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_placeU_mem_emb (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [Algebra ℤ_[p] R] (σ : OE →+* R) :
    ∃ w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE,
      σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e := by sorry
