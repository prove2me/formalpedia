-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_apply_mem_irreducibleComponent_iff_of_generalizingMap
-- name    : FunctorialResolution.EmbeddedResolution.apply_mem_irreducibleComponent_iff_of_generalizingMap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:27.73954+00:00
-- url     : https://prove2.me/theorems/81326639-5e43-4d3c-9e2d-afc34b248da6
-- title:
--   Embedded Resolution: apply mem irreducible Component iff of generalizing Map
-- statement:
--   The Embedded Resolution construction uses the apply mem irreducible Component iff of generalizing Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/IrreducibleComponentsFlatPreimage.lean#L10-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/IrreducibleComponentsFlatPreimage.lean#L10-L41

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IrreducibleComponentsFlatPreimage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.apply_mem_irreducibleComponent_iff_of_generalizingMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : GeneralizingMap (fun x : ↥X => f x))
    {C : Set ↥Y} (hC : C ∈ irreducibleComponents ↥Y) (x : ↥X) :
    (fun x : ↥X => f x) x ∈ C ↔
      ∃ C' : Set ↥X, C' ∈ irreducibleComponents ↥X ∧ x ∈ C' ∧
        closure ((fun x : ↥X => f x) '' C') = C := by sorry
