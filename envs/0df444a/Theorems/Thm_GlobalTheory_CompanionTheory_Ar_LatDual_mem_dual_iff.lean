-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_LatDual_mem_dual_iff
-- name    : GlobalTheory.CompanionTheory.Ar.LatDual.mem_dual_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:19:05.509264+00:00
-- url     : https://prove2.me/theorems/7e17e7f1-0ced-48d0-9ac0-30679a9127d9
-- title:
--   Lat Dual: mem dual iff
-- statement:
--   The Lat Dual construction uses the mem dual iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/IsVBOnDualAndBidual.lean#L39-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/IsVBOnDualAndBidual.lean#L39-L66

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

theorem GlobalTheory.CompanionTheory.Ar.LatDual.mem_dual_iff (L : Lat ξ E) (p : Cpt ξ) {r : ℕ} (b : Fin r → E)
    (h : L p = Submodule.span (regAt ξ p) (Set.range b)) (w : Module.Dual Ω E) :
    w ∈ L.dual p ↔ ∀ i, w (b i) ∈ regAt ξ p := by sorry
