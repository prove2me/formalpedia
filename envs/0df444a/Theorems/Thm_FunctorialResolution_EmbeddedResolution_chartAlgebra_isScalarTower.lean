-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartAlgebra_isScalarTower
-- name    : FunctorialResolution.EmbeddedResolution.chartAlgebra_isScalarTower
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:44.151151+00:00
-- url     : https://prove2.me/theorems/b96f2de8-3e82-4323-8eac-9221134cdc01
-- title:
--   Embedded Resolution: chart Algebra is Scalar Tower
-- statement:
--   The Embedded Resolution construction uses the chart Algebra is Scalar Tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartAlgebra.lean#L56-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartAlgebra.lean#L56-L66

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

theorem FunctorialResolution.EmbeddedResolution.chartAlgebra_isScalarTower (hW : IsAffineOpen W) (h : Y ⟶ X) (e : V ≤ h ⁻¹ᵁ W)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme)
    (hg : g ≫ (AffineSpace n W.toScheme ↘ W.toScheme) = h.resLE W V e) :
    letI : Algebra Γ(X, W) Γ(Y, V) := (h.appLE W V e).hom.toAlgebra
    letI : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
    IsScalarTower Γ(X, W) (MvPolynomial n Γ(X, W)) Γ(Y, V) := by sorry
