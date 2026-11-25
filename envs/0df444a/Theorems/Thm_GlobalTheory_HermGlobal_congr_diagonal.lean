-- Prove2me | Theorems.Thm_GlobalTheory_HermGlobal_congr_diagonal
-- name    : GlobalTheory.HermGlobal.congr_diagonal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:41:43.659976+00:00
-- url     : https://prove2.me/theorems/6d4ac835-47e6-40c1-a308-ce09533f3066
-- title:
--   Herm Global: congr diagonal
-- statement:
--   The Herm Global construction uses the congr diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean#L278-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean#L278-L329

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_congr_diagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass
open GlobalTheory GlobalTheory.HermGlobal
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E}

theorem GlobalTheory.HermGlobal.congr_diagonal (hc : ∀ t, σ (σ t) = t)
    (hF : ∀ t : E, σ t = t ↔ ∃ s : F, algebraMap F E s = t) {θ : E} (hθ0 : θ ≠ 0) (hθ : σ θ = -θ)
    (r : ℕ) : ∀ g g' : Fin r → E,
    (∀ i, σ (g i) = g i) → (∀ i, σ (g' i) = g' i) → (∀ i, g i ≠ 0) → (∀ i, g' i ≠ 0) →
    (∀ τ : E →+* ℂ, (∀ x, τ (σ x) = conj (τ x)) → posCount τ g = posCount τ g') →
    (∃ x : E, ∏ i, g i = x * σ x * ∏ i, g' i) →
    Congr (σ : E →+* E) (Matrix.diagonal g) (Matrix.diagonal g') := by sorry
