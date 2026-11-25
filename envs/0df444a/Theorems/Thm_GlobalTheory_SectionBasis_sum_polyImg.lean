-- Prove2me | Theorems.Thm_GlobalTheory_SectionBasis_sum_polyImg
-- name    : GlobalTheory.SectionBasis.sum_polyImg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:28:49.233799+00:00
-- url     : https://prove2.me/theorems/51769c3a-c09c-4513-b1e0-0c3dd7f6a8be
-- title:
--   Section Basis: sum poly Img
-- statement:
--   The Section Basis construction uses the sum poly Img property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsDvdOfAlgebraic.lean#L113-L120

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
variable {K Ω K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field K'] [Algebra K K'] {D N : ℕ}

theorem GlobalTheory.SectionBasis.sum_polyImg (j0 : Fin (N + 1)) (v : Fin (N + 1) → Ω) (x : Fin N → Ω) (hv : v j0 ≠ 0)
    (hx : ∀ k, x k = v (j0.succAbove k) / v j0) (i : Fin (D + 1)) :
    ∑ j, polyImg j0 x (i, j) * C (v j) =
      C (v j0) * (polyImg j0 x (i, j0) + ∑ k, X (Sum.inr (i, k)) * C (x k)) := by sorry
