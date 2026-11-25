-- Prove2me | Theorems.Thm_GlobalTheory_Published_HermitianHassePrinciple_iff
-- name    : GlobalTheory.Published.HermitianHassePrinciple.iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:55.287206+00:00
-- url     : https://prove2.me/theorems/23868eb5-2e92-51f3-bccf-5aa716070eea
-- title:
--   Hermitian Hasse Principle: iff
-- statement:
--   The Hermitian Hasse Principle construction uses the iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean#L449-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/HermitianHassePrincipleHolds.lean#L449-L457

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det
import Theorems.Thm_GlobalTheory_Published_Landherr_iff

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
open GlobalTheory GlobalTheory.Published
open GlobalTheory.HermGlobal

theorem GlobalTheory.Published.HermitianHassePrinciple.iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Algebra.IsQuadraticExtension F E] {σ : E ≃ₐ[F] E} (hσ : σ ≠ 1) {r : ℕ}
    {G G' : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, σ (G a b) = G b a)
    (hG' : ∀ a b, σ (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ) ↔
      (∀ v : HeightOneSpectrum (𝓞 F), CongrOver σ (v.adicCompletion F) G G') ∧
        ∀ v : InfinitePlace F, CongrOver σ v.Completion G G' := by sorry
