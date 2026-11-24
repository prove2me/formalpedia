-- Prove2me | Theorems.Thm_GlobalTheory_HermGlobal_CongrOver_complex
-- name    : GlobalTheory.HermGlobal.CongrOver.complex
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:10:09.05886+00:00
-- url     : https://prove2.me/theorems/e35afa18-b152-42f4-9647-65708ebf8903
-- title:
--   Congr Over: complex
-- statement:
--   The Congr Over construction uses the complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean#L56-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean#L56-L85

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
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {A : Type*} [CommRing A] [Algebra F A] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}

theorem GlobalTheory.HermGlobal.CongrOver.complex (h : CongrOver σ A G G') (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = conj (τ x))
    (ψ : A →+* ℂ) (hψ : ∀ a, conj (ψ a) = ψ a)
    (hψτ : ∀ s : F, ψ (algebraMap F A s) = τ (algebraMap F E s)) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map τ = Qᵀ * G.map τ * Q.map conj := by sorry
