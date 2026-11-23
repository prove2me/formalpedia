-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_injective
-- name    : GlobalTheory.CompanionTheory.Ultra.pt_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:25.230172+00:00
-- url     : https://prove2.me/theorems/412bbe18-e797-49a5-b01b-2529f54c4e50
-- title:
--   Ultra: pt injective
-- statement:
--   The Ultra construction uses the pt injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L301-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L301-L305

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

theorem GlobalTheory.CompanionTheory.Ultra.pt_injective (W : X.affineOpens) {A : Type} [CommRing A] {p q : Γ(X, W.1) →+* A}
    (h : pt W p = pt W q) : p = q := by sorry
