-- Prove2me | Theorems.Thm_GlobalTheory_HermGlobal_involutive_and_fixed
-- name    : GlobalTheory.HermGlobal.involutive_and_fixed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:12:53.34812+00:00
-- url     : https://prove2.me/theorems/4a4a2373-eadf-4d4e-85cc-4bc8c371b08b
-- title:
--   Herm Global: involutive and fixed
-- statement:
--   The Herm Global construction uses the involutive and fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean#L93-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean#L93-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
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

theorem GlobalTheory.HermGlobal.involutive_and_fixed [Algebra.IsQuadraticExtension F E] {σ : E ≃ₐ[F] E} (hσ : σ ≠ 1) :
    (∀ t, σ (σ t) = t) ∧ (∀ t : E, σ t = t ↔ ∃ s : F, algebraMap F E s = t) ∧
      ∃ θ : E, θ ≠ 0 ∧ σ θ = -θ := by sorry
