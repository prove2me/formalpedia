-- Prove2me | Theorems.Thm_GlobalTheory_HermGlobal_congr_of_local_complex
-- name    : GlobalTheory.HermGlobal.congr_of_local_complex
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:12:25.434153+00:00
-- url     : https://prove2.me/theorems/4e14db4a-d6a8-465f-9057-fd166ae5e098
-- title:
--   Herm Global: congr of local complex
-- statement:
--   The Herm Global construction uses the congr of local complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean#L375-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean#L375-L409

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det

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
variable [Algebra.IsQuadraticExtension F E] {r : ℕ} {G G' : Matrix (Fin r) (Fin r) E}

theorem GlobalTheory.HermGlobal.congr_of_local_complex (hσ : σ ≠ 1) (hG : ∀ a b, σ (G a b) = G b a)
    (hG' : ∀ a b, σ (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), CongrOver σ (v.adicCompletion F) G G')
    (hi : ∀ τ : E →+* ℂ, (∀ x, τ (σ x) = conj (τ x)) → ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ := by sorry
