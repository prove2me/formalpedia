-- Prove2me | Theorems.Thm_GlobalTheory_SectionBasis_incl_apply
-- name    : GlobalTheory.SectionBasis.incl_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:28:43.216812+00:00
-- url     : https://prove2.me/theorems/7dcf1110-27d4-4f0d-b603-0625a1eb7964
-- title:
--   Section Basis: incl apply
-- statement:
--   The Section Basis construction uses the incl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L22-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L22-L22

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

theorem GlobalTheory.SectionBasis.incl_apply (ω : Ω) : incl K Kl K' ω = (1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω) := by sorry
