-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartEvalHom_comp_C
-- name    : FunctorialResolution.EmbeddedResolution.chartEvalHom_comp_C
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:46.678005+00:00
-- url     : https://prove2.me/theorems/e06a54e3-2952-4a6a-8fb8-b17999618da6
-- title:
--   Embedded Resolution: chart Eval Hom comp C
-- statement:
--   The Embedded Resolution construction uses the chart Eval Hom comp C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartAlgebra.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartAlgebra.lean#L33-L42

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartAlgebra
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
variable {X Y : Scheme.{u}} {W : X.Opens} {V : Y.Opens} {n : Type u}

theorem FunctorialResolution.EmbeddedResolution.chartEvalHom_comp_C (hW : IsAffineOpen W) (h : Y ⟶ X) (e : V ≤ h ⁻¹ᵁ W)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme)
    (hg : g ≫ (AffineSpace n W.toScheme ↘ W.toScheme) = h.resLE W V e) :
    (chartEvalHom hW g).comp (MvPolynomial.C : Γ(X, W) →+* MvPolynomial n Γ(X, W)) =
      (h.appLE W V e).hom := by sorry
