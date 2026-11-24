-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_lat_restrict_comap_span
-- name    : GlobalTheory.CompanionTheory.Ar.lat_restrict_comap_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:43.32478+00:00
-- url     : https://prove2.me/theorems/2b90490d-ee55-4c50-bdd8-30c6ebf1d77a
-- title:
--   Ar: lat restrict comap span
-- statement:
--   The Ar construction uses the lat restrict comap span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/LatRestrictComapSpan.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/LatRestrictComapSpan.lean#L7-L14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar

theorem GlobalTheory.CompanionTheory.Ar.lat_restrict_comap_span {Ω R E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [Semiring R] [SMul R Ω]
    [Module R E] [IsScalarTower R Ω E] (V : Submodule Ω E) {r : ℕ} (b : Fin r → V) :
    (Submodule.span R (Set.range fun i => (b i : E))).comap (V.subtype.restrictScalars R) =
      Submodule.span R (Set.range b) := by sorry
