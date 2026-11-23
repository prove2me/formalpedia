-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_homOf_apply
-- name    : GlobalTheory.CompanionTheory.Ultra.homOf_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:34.767733+00:00
-- url     : https://prove2.me/theorems/928d6472-c66c-4c18-b649-5a0e7e95a96b
-- title:
--   Ultra: hom Of apply
-- statement:
--   The Ultra construction uses the hom Of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L207-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L207-L208

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {ι : Type} (U : Ultrafilter ι)
variable {A : ι → Type} [∀ i, CommRing (A i)] {B : Type} [CommRing B]

theorem GlobalTheory.CompanionTheory.Ultra.homOf_apply (h : ∀ i, B → A i) (hh : IsAEHom U h) (b : B) :
    homOf U h hh b = mk U (fun i => h i b) := by sorry
