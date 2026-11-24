-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_LatDual_mem_span_basis_iff
-- name    : GlobalTheory.CompanionTheory.Ar.LatDual.mem_span_basis_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:36.001367+00:00
-- url     : https://prove2.me/theorems/7eb199d4-3189-4ca8-8d3f-055e6ab0bb82
-- title:
--   Lat Dual: mem span basis iff
-- statement:
--   The Lat Dual construction uses the mem span basis iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/IsVBOnDualAndBidual.lean#L11-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/IsVBOnDualAndBidual.lean#L11-L37

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LatDual
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem GlobalTheory.CompanionTheory.Ar.LatDual.mem_span_basis_iff (p : Cpt ξ) {r : ℕ} (B : Module.Basis (Fin r) Ω E) (e : E) :
    e ∈ Submodule.span (regAt ξ p) (Set.range B) ↔ ∀ i, B.repr e i ∈ regAt ξ p := by sorry
