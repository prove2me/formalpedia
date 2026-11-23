-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_mem
-- name    : GlobalTheory.CompanionTheory.Ultra.pt_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:12.41+00:00
-- url     : https://prove2.me/theorems/a8532344-b244-4c22-b227-e6c08f795f51
-- title:
--   Ultra: pt mem
-- statement:
--   The Ultra construction uses the pt mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L316-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L316-L321

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

theorem GlobalTheory.CompanionTheory.Ultra.pt_mem (W : X.affineOpens) {A : Type} [CommRing A] (p : Γ(X, W.1) →+* A)
    (x : Spec (CommRingCat.of A)) : (pt W p) x ∈ W.1 := by sorry
