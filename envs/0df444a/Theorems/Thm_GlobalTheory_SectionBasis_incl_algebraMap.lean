-- Prove2me | Theorems.Thm_GlobalTheory_SectionBasis_incl_algebraMap
-- name    : GlobalTheory.SectionBasis.incl_algebraMap
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:51:57.125084+00:00
-- url     : https://prove2.me/theorems/a5d847e3-dcb8-58fd-8aea-97a6ea756f50
-- title:
--   Section Basis: incl algebra Map
-- statement:
--   The Section Basis construction uses the incl algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L24-L29

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

theorem GlobalTheory.SectionBasis.incl_algebraMap (c : K) :
    incl K Kl K' (algebraMap K Ω c) = algebraMap K' (K' ⊗[Kl] (Kl ⊗[K] Ω)) (algebraMap K K' c) := by sorry
