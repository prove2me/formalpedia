-- Prove2me | Theorems.Thm_GlobalTheory_HermGlobal_CongrOver_exists_sq_sub
-- name    : GlobalTheory.HermGlobal.CongrOver.exists_sq_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:11:30.657009+00:00
-- url     : https://prove2.me/theorems/83258593-3243-4963-a287-97f622e3749c
-- title:
--   Congr Over: exists sq sub
-- statement:
--   The Congr Over construction uses the exists sq sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean#L141-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean#L141-L173

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
variable {σ : E ≃ₐ[F] E}

theorem GlobalTheory.HermGlobal.CongrOver.exists_sq_sub [CharZero E] (hc : ∀ t, σ (σ t) = t)
    (hF : ∀ t : E, σ t = t ↔ ∃ s : F, algebraMap F E s = t) {θ : E} (h0 : θ ≠ 0) (hθ : σ θ = -θ)
    {d : F} (hd : algebraMap F E d = θ * θ) {A : Type*} [Field A] [Algebra F A] {r : ℕ}
    {G G' : Matrix (Fin r) (Fin r) E} (hd' : G'.det ≠ 0) (h : CongrOver σ A G G') {a : F}
    (ha : algebraMap F E a = G.det / G'.det) :
    ∃ p q : A, algebraMap F A a = p ^ 2 - algebraMap F A d * q ^ 2 := by sorry
