-- Prove2me | Theorems.Thm_GaussValuationUniqueness_imgR_succAbove
-- name    : GaussValuationUniqueness.imgR_succAbove
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:50:38.74213+00:00
-- url     : https://prove2.me/theorems/a890afa1-6b6a-4586-b35b-7136c68962a0
-- title:
--   Gauss Valuation Uniqueness: img R succ Above
-- statement:
--   The Gauss Valuation Uniqueness construction uses the img R succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ImgRSuccAbove.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ImgRSuccAbove.lean#L20-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ExistsSmulOfLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ImgRSuccAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GaussValuationUniqueness
open ReciprocityTheory.ChartRestriction.G.T0

theorem GaussValuationUniqueness.imgR_succAbove {R : Type*} [CommRing R] {D N : ℕ} (j0 : Fin (N + 1)) (ρ : Fin N → R)
    (i : Fin (D + 1)) (k : Fin N) :
    imgR (D := D) j0 ρ (i, j0.succAbove k) = MvPolynomial.X (Sum.inr (i, k)) := by sorry
