-- Prove2me | Theorems.Thm_GlobalTheory_HermLocal_congr_of_local
-- name    : GlobalTheory.HermLocal.congr_of_local
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:55:19.783524+00:00
-- url     : https://prove2.me/theorems/e7ceaef7-535d-4642-847e-6aa56fab979f
-- title:
--   Herm Local: congr of local
-- statement:
--   The Herm Local construction uses the congr of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean#L328-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean#L328-L372

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {A : Type*} [CommRing A] [Algebra (maximalRealSubfield E) A] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}

theorem GlobalTheory.HermLocal.congr_of_local (hG : ∀ a b, cc (G a b) = G b a) (hG' : ∀ a b, cc (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      CongrOver (v.adicCompletion (maximalRealSubfield E)) G G')
    (hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc := by sorry
