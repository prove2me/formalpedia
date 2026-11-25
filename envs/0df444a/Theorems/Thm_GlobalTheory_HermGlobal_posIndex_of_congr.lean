-- Prove2me | Theorems.Thm_GlobalTheory_HermGlobal_posIndex_of_congr
-- name    : GlobalTheory.HermGlobal.posIndex_of_congr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:16:20.260061+00:00
-- url     : https://prove2.me/theorems/105f6f75-f340-523a-bacf-af5323430734
-- title:
--   Herm Global: pos Index of congr
-- statement:
--   The Herm Global construction uses the pos Index of congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean#L267-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean#L267-L276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_posIndex_of_congr

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
omit [NumberField F] [NumberField E]

theorem GlobalTheory.HermGlobal.posIndex_of_congr {τ : E →+* ℂ} (hτ : ∀ x, τ (σ x) = conj (τ x)) {r : ℕ}
    {G G' : Matrix (Fin r) (Fin r) E} (h : Congr (σ : E →+* E) G G') :
    GlobalTheory.Inertia.posIndex (G'.map τ) = GlobalTheory.Inertia.posIndex (G.map τ) := by sorry
