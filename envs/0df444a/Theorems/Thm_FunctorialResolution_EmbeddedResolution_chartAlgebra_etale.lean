-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartAlgebra_etale
-- name    : FunctorialResolution.EmbeddedResolution.chartAlgebra_etale
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:39.378858+00:00
-- url     : https://prove2.me/theorems/fd0d31a2-18a7-446e-bde7-339f1a8b9812
-- title:
--   Embedded Resolution: chart Algebra etale
-- statement:
--   The Embedded Resolution construction uses the chart Algebra etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartAlgebra.lean#L175-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartAlgebra.lean#L175-L201

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

theorem FunctorialResolution.EmbeddedResolution.chartAlgebra_etale (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme) [Etale g] :
    letI : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
    Algebra.Etale (MvPolynomial n Γ(X, W)) Γ(Y, V) := by sorry
