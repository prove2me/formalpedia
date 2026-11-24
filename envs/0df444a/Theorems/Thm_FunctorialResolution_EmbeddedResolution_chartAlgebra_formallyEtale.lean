-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartAlgebra_formallyEtale
-- name    : FunctorialResolution.EmbeddedResolution.chartAlgebra_formallyEtale
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:38.975232+00:00
-- url     : https://prove2.me/theorems/7ad56614-355a-4ce3-b0ad-05e2a5337bdc
-- title:
--   Embedded Resolution: chart Algebra formally Etale
-- statement:
--   The Embedded Resolution construction uses the chart Algebra formally Etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartAlgebra.lean#L203-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartAlgebra.lean#L203-L209

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

theorem FunctorialResolution.EmbeddedResolution.chartAlgebra_formallyEtale (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme) [Etale g] :
    letI : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
    Algebra.FormallyEtale (MvPolynomial n Γ(X, W)) Γ(Y, V) := by sorry
