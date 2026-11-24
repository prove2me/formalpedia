-- Prove2me | Theorems.Thm_GlobalTheory_HermLocal_CongrOver_det_norm
-- name    : GlobalTheory.HermLocal.CongrOver.det_norm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:44:45.62378+00:00
-- url     : https://prove2.me/theorems/964fe9a0-ff69-4024-a88a-ddede9a79110
-- title:
--   Congr Over: det norm
-- statement:
--   The Congr Over construction uses the det norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean#L310-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ExistsOrthonormalOfUnimodular.lean#L310-L326

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det
import Theorems.Thm_GlobalTheory_Published_Landherr_det_norm

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

theorem GlobalTheory.HermLocal.CongrOver.det_norm (hd' : G'.det ≠ 0) (h : CongrOver A G G') :
    ∃ z : A ⊗[maximalRealSubfield E] E,
      (1 : A) ⊗ₜ[maximalRealSubfield E] (G.det / G'.det) = z * ccBase E A z := by sorry
