-- Prove2me | Theorems.Thm_GlobalTheory_residueField_map_finite_of_quasiFinite
-- name    : GlobalTheory.residueField_map_finite_of_quasiFinite
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:07.767267+00:00
-- url     : https://prove2.me/theorems/84e6039c-8c0b-42ee-9a4b-f0f3a3d78f1b
-- title:
--   Global Theory: residue Field map finite of quasi Finite
-- statement:
--   The Global Theory construction uses the residue Field map finite of quasi Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ResidueFieldMapFiniteOfQuasiFinite.lean#L6-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ResidueFieldMapFiniteOfQuasiFinite.lean#L6-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldMapFiniteOfQuasiFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory

theorem GlobalTheory.residueField_map_finite_of_quasiFinite {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (h : f.QuasiFinite) :
    (IsLocalRing.ResidueField.map f).Finite := by sorry
