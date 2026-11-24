-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_IsQuad_exists_base_value
-- name    : GlobalTheory.QNorm.IsQuad.exists_base_value
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:02:32.58373+00:00
-- url     : https://prove2.me/theorems/8f8aca65-764c-4a53-892c-e814460ad736
-- title:
--   Is Quad: exists base value
-- statement:
--   The Is Quad construction uses the exists base value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ValuationUnramifiedOfUnit.lean#L9-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ValuationUnramifiedOfUnit.lean#L9-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HeightOneSpectrumPlacesOverFiniteSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationUnramifiedOfUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.IsQuad.exists_base_value {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsQuad δ θ σ) (w : Valuation E ℤᵐ⁰) (h2 : w 2 = 1)
    (hδ : w (algebraMap F E δ) = 1) (x : E) : ∃ u : F, w x = w (algebraMap F E u) := by sorry
