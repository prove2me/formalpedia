-- Prove2me | Theorems.Thm_GlobalTheory_residue_eval_map_eq_aeval
-- name    : GlobalTheory.residue_eval_map_eq_aeval
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:16:11.050106+00:00
-- url     : https://prove2.me/theorems/307acfe7-104b-4426-8963-859de35f51b3
-- title:
--   Global Theory: residue eval map eq aeval
-- statement:
--   The Global Theory construction uses the residue eval map eq aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPrimitiveElementComplete.lean#L6-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPrimitiveElementComplete.lean#L6-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimitiveElementComplete
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

theorem GlobalTheory.residue_eval_map_eq_aeval {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] (φ : A →+* R) [IsLocalHom φ] (P : A[X]) (x : R) :
    letI := (ResidueField.map φ).toAlgebra
    residue R ((P.map φ).eval x) = aeval (residue R x) (P.map (residue A)) := by sorry
