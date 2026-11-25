-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_exists_smoothLocus
-- name    : GlobalTheory.WeierstrassCurve.exists_smoothLocus
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:43.739371+00:00
-- url     : https://prove2.me/theorems/f1a25e1b-c5a0-4d8c-88e1-603d363d2b37
-- title:
--   Weierstrass Curve: exists smooth Locus
-- statement:
--   The Weierstrass Curve construction uses the exists smooth Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TopLePtHomPreimageSmoothOpenIff.lean#L187-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TopLePtHomPreimageSmoothOpenIff.lean#L187-L194

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TopLePtHomPreimageSmoothOpenIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem GlobalTheory.WeierstrassCurve.exists_smoothLocus (R : Type) [CommRing R] (W : WeierstrassCurve R) :
    ∃ U : (scheme W).Opens, (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k)
      (h : IsUnimodularSol (W.map ρ) P),
        ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) ∧
      SmoothOfRelativeDimension 1 (U.ι ≫ toSpec W) ∧ QuasiCompact (U.ι ≫ toSpec W) ∧
      GeometricallyIntegral (U.ι ≫ toSpec W) := by sorry
