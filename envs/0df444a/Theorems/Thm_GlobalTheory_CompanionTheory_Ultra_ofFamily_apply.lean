-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_ofFamily_apply
-- name    : GlobalTheory.CompanionTheory.Ultra.ofFamily_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:19:34.272285+00:00
-- url     : https://prove2.me/theorems/1660add9-37dc-46cb-90eb-d929a4d866fe
-- title:
--   Ultra: of Family apply
-- statement:
--   The Ultra construction uses the of Family apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L198-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L198-L199

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

theorem GlobalTheory.CompanionTheory.Ultra.ofFamily_apply (h : ∀ i, B → A i) (h1 hadd hmul) (b : B) :
    ofFamily U h h1 hadd hmul b = mk U (fun i => h i b) := by sorry
