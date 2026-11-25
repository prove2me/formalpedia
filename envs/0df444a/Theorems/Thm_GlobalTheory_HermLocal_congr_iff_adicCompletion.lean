-- Prove2me | Theorems.Thm_GlobalTheory_HermLocal_congr_iff_adicCompletion
-- name    : GlobalTheory.HermLocal.congr_iff_adicCompletion
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:22.908555+00:00
-- url     : https://prove2.me/theorems/50b333cf-03fb-4b8b-b9d3-d85b43298a6d
-- title:
--   Herm Local: congr iff adic Completion
-- statement:
--   The Herm Local construction uses the congr iff adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean#L268-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean#L268-L278

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
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
open scoped Matrix TensorProduct ComplexConjugate WithZero
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass
open GlobalTheory GlobalTheory.HermLocal

theorem GlobalTheory.HermLocal.congr_iff_adicCompletion (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (L : Type*) [Field L] [Algebra (v.adicCompletion F) L]
    [Algebra.IsQuadraticExtension (v.adicCompletion F) L] (σ : L ≃ₐ[v.adicCompletion F] L)
    (hσ : σ ≠ 1) {r : ℕ} {G G' : Matrix (Fin r) (Fin r) L} (hG : ∀ a b, σ (G a b) = G b a)
    (hG' : ∀ a b, σ (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix (Fin r) (Fin r) L, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ) ↔
      ∃ x : L, G.det / G'.det = x * σ x := by sorry
