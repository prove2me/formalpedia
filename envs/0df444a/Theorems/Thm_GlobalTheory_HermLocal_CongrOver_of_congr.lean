-- Prove2me | Theorems.Thm_GlobalTheory_HermLocal_CongrOver_of_congr
-- name    : GlobalTheory.HermLocal.CongrOver.of_congr
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:56:44.406314+00:00
-- url     : https://prove2.me/theorems/0c2628d0-3a72-4df2-9180-ebf10fe5b539
-- title:
--   Congr Over: of congr
-- statement:
--   The Congr Over construction uses the of congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean#L298-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean#L298-L308

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

theorem GlobalTheory.HermLocal.CongrOver.of_congr
    (h : ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc) :
    CongrOver A G G' := by sorry
