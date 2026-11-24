-- Prove2me | Theorems.Thm_GlobalTheory_PairingLocus_exists_idempotent
-- name    : GlobalTheory.PairingLocus.exists_idempotent
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:41:02.501647+00:00
-- url     : https://prove2.me/theorems/dabd2bdb-6940-4bc3-a89c-99f865115e87
-- title:
--   Pairing Locus: exists idempotent
-- statement:
--   The Pairing Locus construction uses the exists idempotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsClopenOfIsLocallyNoetherian.lean#L12-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsClopenOfIsLocallyNoetherian.lean#L12-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsClopenOfIsLocallyNoetherian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLocus

theorem GlobalTheory.PairingLocus.exists_idempotent {R : Type} [CommRing R] {n : ℕ} (hn : IsUnit (n : R)) {u : R} (hu : u ^ n = 1) :
    ∃ e : R, IsIdempotentElem e ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), φ u = 1 ↔ φ e = 1 := by sorry
