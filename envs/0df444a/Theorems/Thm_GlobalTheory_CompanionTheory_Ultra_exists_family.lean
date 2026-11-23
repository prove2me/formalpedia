-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_family
-- name    : GlobalTheory.CompanionTheory.Ultra.exists_family
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:21.023961+00:00
-- url     : https://prove2.me/theorems/35aa48fe-2fd3-4f7f-8f5e-ab8bccf76f39
-- title:
--   Ultra: exists family
-- statement:
--   The Ultra construction uses the exists family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L216-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L216-L222

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

theorem GlobalTheory.CompanionTheory.Ultra.exists_family {Q : ∀ i, (B →+* A i) → Prop}
    (H : ∀ᶠ i in (U : Filter ι), ∃ p : B →+* A i, Q i p) :
    ∃ h : ∀ i, B → A i, ∀ᶠ i in (U : Filter ι), ∃ p : B →+* A i, ⇑p = h i ∧ Q i p := by sorry
