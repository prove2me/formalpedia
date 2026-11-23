-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_pt_of_isLocalRing
-- name    : GlobalTheory.CompanionTheory.Ultra.exists_pt_of_isLocalRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:22.097274+00:00
-- url     : https://prove2.me/theorems/7ff38038-bd88-4b83-b5a5-e608983bdb0e
-- title:
--   Ultra: exists pt of is Local Ring
-- statement:
--   The Ultra construction uses the exists pt of is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L323-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L323-L332

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X : Scheme.{0}}

theorem GlobalTheory.CompanionTheory.Ultra.exists_pt_of_isLocalRing {A : Type} [CommRing A] [IsLocalRing A]
    (g : Spec (CommRingCat.of A) ⟶ X) (W : X.affineOpens)
    (hW : g (IsLocalRing.closedPoint A : PrimeSpectrum A) ∈ W.1) : ∃ p, g = pt W p := by sorry
