-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_TraceIsometry_exists_linearMap_isometry
-- name    : GlobalTheory.LocalQuad.TraceIsometry.exists_linearMap_isometry
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:14:14.166381+00:00
-- url     : https://prove2.me/theorems/de8cc5e0-16d3-4d97-991c-c2021c7be7e8
-- title:
--   Trace Isometry: exists linear Map isometry
-- statement:
--   The Trace Isometry construction uses the exists linear Map isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometric.lean#L112-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometric.lean#L112-L165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.LocalQuad GlobalTheory.LocalQuad.TraceIsometry
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {c : E →+* E}
universe u v in

theorem GlobalTheory.LocalQuad.TraceIsometry.exists_linearMap_isometry (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t) (d : ℕ) :
    ∀ {V : Type u} {W : Type v} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
      [FiniteDimensional E V] [AddCommGroup W] [Module E W] [Module F W] [IsScalarTower F E W]
      (B : V →ₗ[E] V →ₛₗ[c] E) (B' : W →ₗ[E] W →ₛₗ[c] E),
      (∀ x y, c (B x y) = B y x) → (∀ x y, c (B' x y) = B' y x) → finrank E V = d →
      ∀ φ : V →ₗ[F] W, (∀ x, B' (φ x) (φ x) = B x x) →
      ∃ ψ : V →ₗ[E] W, ∀ x y, B' (ψ x) (ψ y) = B x y := by sorry
