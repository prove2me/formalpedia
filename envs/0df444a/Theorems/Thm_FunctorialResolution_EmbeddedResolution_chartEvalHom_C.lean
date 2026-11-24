-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartEvalHom_C
-- name    : FunctorialResolution.EmbeddedResolution.chartEvalHom_C
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:47.930441+00:00
-- url     : https://prove2.me/theorems/21cf5037-ace0-45ea-b7a6-298c2b22d967
-- title:
--   Embedded Resolution: chart Eval Hom C
-- statement:
--   The Embedded Resolution construction uses the chart Eval Hom C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartAlgebra.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartAlgebra.lean#L44-L48

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

theorem FunctorialResolution.EmbeddedResolution.chartEvalHom_C (hW : IsAffineOpen W) (h : Y ⟶ X) (e : V ≤ h ⁻¹ᵁ W)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme)
    (hg : g ≫ (AffineSpace n W.toScheme ↘ W.toScheme) = h.resLE W V e) (a : Γ(X, W)) :
    chartEvalHom hW g (MvPolynomial.C a) = (h.appLE W V e).hom a := by sorry
