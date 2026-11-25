-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_adic_coordinates_of_basis_mod_p
-- name    : GlobalTheory.T.exists_adic_coordinates_of_basis_mod_p
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:14.934551+00:00
-- url     : https://prove2.me/theorems/3f4cb07f-9e0f-527b-8a7f-9c84b12b558c
-- title:
--   T: exists adic coordinates of basis mod p
-- statement:
--   The T construction uses the exists adic coordinates of basis mod p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAdicCoordinatesOfBasisModPStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAdicCoordinatesOfBasisModPStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAdicCoordinatesOfBasisModP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAdicCoordinatesOfBasisModPStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_adic_coordinates_of_basis_mod_p : ∀ (p : ℕ) (O EE W RW : Type) [CommRing O] [CommRing EE] [CommRing W] [CommRing RW] [Algebra O EE] [Algebra O RW] (ι : EE →ₐ[O] RW) (c : W →+* RW) (d : ℕ) (o : Fin d → O), (∀ r : RW, ∃! w : Fin d → W, r = ∑ j, o j • c (w j)) → IsAdicComplete (Ideal.span {(p : EE)}) EE → IsAdicComplete (Ideal.span {(p : W)}) W → (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e - ∑ j, o j • e' j ∈ Ideal.span {(p : EE)}) → ∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j := by sorry
