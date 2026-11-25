-- Prove2me | Theorems.Thm_GlobalTheory_SectionBasis_tmul_eq
-- name    : GlobalTheory.SectionBasis.tmul_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:52:05.421041+00:00
-- url     : https://prove2.me/theorems/c3ed9b35-ac1a-42d2-af65-3350233cab47
-- title:
--   Section Basis: tmul eq
-- statement:
--   The Section Basis construction uses the tmul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L31-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
variable {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
  [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']

theorem GlobalTheory.SectionBasis.tmul_eq (a : K') (ω : Ω) : a ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω) =
    algebraMap K' (K' ⊗[Kl] (Kl ⊗[K] Ω)) a * incl K Kl K' ω := by sorry
