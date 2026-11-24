-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SmoothEtaleChart_exists_isAffineOpen_etale_resLE_le
-- name    : FunctorialResolution.EmbeddedResolution.SmoothEtaleChart.exists_isAffineOpen_etale_resLE_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:46:54.419478+00:00
-- url     : https://prove2.me/theorems/fb9df1ca-4534-4cb3-9f9f-5206e276e63c
-- title:
--   Smooth Etale Chart: exists is Affine Open etale res LE le
-- statement:
--   The Smooth Etale Chart construction uses the exists is Affine Open etale res LE le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothEtaleChart.lean#L121-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothEtaleChart.lean#L121-L128

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothEtaleChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.SmoothEtaleChart

theorem FunctorialResolution.EmbeddedResolution.SmoothEtaleChart.exists_isAffineOpen_etale_resLE_le {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h]
    (y : Y) (W₀ : X.Opens) (hW₀ : h.base y ∈ W₀) (V₀ : Y.Opens) (hV₀ : y ∈ V₀) :
    ∃ (W : X.Opens) (V : Y.Opens) (d : ℕ) (e : V ≤ h ⁻¹ᵁ W),
      IsAffineOpen W ∧ IsAffineOpen V ∧ y ∈ V ∧ W ≤ W₀ ∧ V ≤ V₀ ∧
      ∃ g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme,
        Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e := by sorry
