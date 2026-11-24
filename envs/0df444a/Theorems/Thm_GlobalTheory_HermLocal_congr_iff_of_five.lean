-- Prove2me | Theorems.Thm_GlobalTheory_HermLocal_congr_iff_of_five
-- name    : GlobalTheory.HermLocal.congr_iff_of_five
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:54:46.299969+00:00
-- url     : https://prove2.me/theorems/597303b5-6bf3-4ee8-b77c-1beef7f1e5be
-- title:
--   Herm Local: congr iff of five
-- statement:
--   The Herm Local construction uses the congr iff of five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean#L146-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean#L146-L207

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
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {c : L →+* L}

theorem GlobalTheory.HermLocal.congr_iff_of_five (h2 : (2 : K) ≠ 0)
    (H : ∀ a : Fin 5 → K, ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0)
    [Algebra.IsQuadraticExtension K L] (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) {r : ℕ}
    {G G' : Matrix (Fin r) (Fin r) L} (hG : ∀ a b, σ (G a b) = G b a)
    (hG' : ∀ a b, σ (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix (Fin r) (Fin r) L, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ) ↔
      ∃ x : L, G.det / G'.det = x * σ x := by sorry
