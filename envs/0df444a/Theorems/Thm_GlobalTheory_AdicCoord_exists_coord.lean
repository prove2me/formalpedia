-- Prove2me | Theorems.Thm_GlobalTheory_AdicCoord_exists_coord
-- name    : GlobalTheory.AdicCoord.exists_coord
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:57:06.336293+00:00
-- url     : https://prove2.me/theorems/2fbf393c-a784-4490-b03c-04b4ddb8dec0
-- title:
--   Adic Coord: exists coord
-- statement:
--   The Adic Coord construction uses the exists coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAdicCoordinatesOfBasisModP.lean#L27-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAdicCoordinatesOfBasisModP.lean#L27-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAdicCoordinatesOfBasisModP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AdicCoord

theorem GlobalTheory.AdicCoord.exists_coord : ∀ (p : ℕ) (O EE W RW : Type) [CommRing O] [CommRing EE] [CommRing W] [CommRing RW] [Algebra O EE] [Algebra O RW] (ι : EE →ₐ[O] RW) (c : W →+* RW) (d : ℕ) (o : Fin d → O), (∀ r : RW, ∃! w : Fin d → W, r = ∑ j, o j • c (w j)) → IsAdicComplete (Ideal.span {(p : EE)}) EE → IsAdicComplete (Ideal.span {(p : W)}) W → (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e - ∑ j, o j • e' j ∈ Ideal.span {(p : EE)}) → ∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j := by sorry
