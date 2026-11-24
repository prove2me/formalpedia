-- Prove2me | Theorems.Thm_GlobalTheory_residue_eval_map_comm
-- name    : GlobalTheory.residue_eval_map_comm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:27.708649+00:00
-- url     : https://prove2.me/theorems/0d374841-f57c-4f6c-9fa9-f9073b2e13a2
-- title:
--   Global Theory: residue eval map comm
-- statement:
--   The Global Theory construction uses the residue eval map comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsHenselRootResidue.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsHenselRootResidue.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHenselRootResidue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory

theorem GlobalTheory.residue_eval_map_comm {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (q : A[X]) (f : A →+* B) (h : B →+* C) (x : B) :
    h ((q.map f).eval x) = (q.map (h.comp f)).eval (h x) := by sorry
