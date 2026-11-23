-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_res
-- name    : GlobalTheory.CompanionTheory.Ultra.pt_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:26.798684+00:00
-- url     : https://prove2.me/theorems/cbf416fc-3079-485c-a0a8-2a7305bab4c0
-- title:
--   Ultra: pt res
-- statement:
--   The Ultra construction uses the pt res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L310-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L310-L314

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

theorem GlobalTheory.CompanionTheory.Ultra.pt_res {W W' : X.affineOpens} (h : W.1 ≤ W'.1) {A : Type} [CommRing A]
    (p : Γ(X, W.1) →+* A) : pt W' (p.comp (res h)) = pt W p := by sorry
