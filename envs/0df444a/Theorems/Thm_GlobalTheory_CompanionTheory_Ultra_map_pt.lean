-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_map_pt
-- name    : GlobalTheory.CompanionTheory.Ultra.map_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:08.336912+00:00
-- url     : https://prove2.me/theorems/c5c75bc9-1976-4c73-8fd9-ef692ddf4c5c
-- title:
--   Ultra: map pt
-- statement:
--   The Ultra construction uses the map pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L296-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L296-L299

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

theorem GlobalTheory.CompanionTheory.Ultra.map_pt (W : X.affineOpens) {A B : Type} [CommRing A] [CommRing B] (p : Γ(X, W.1) →+* A)
    (q : A →+* B) :
    Spec.map (CommRingCat.ofHom q) ≫ pt W p = pt W (q.comp p) := by sorry
