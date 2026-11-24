-- Prove2me | Theorems.Thm_GaussValuationUniqueness_imgR_map
-- name    : GaussValuationUniqueness.imgR_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:51:03.704357+00:00
-- url     : https://prove2.me/theorems/91beb8b8-cec6-4a1c-81ca-096144943720
-- title:
--   Gauss Valuation Uniqueness: img R map
-- statement:
--   The Gauss Valuation Uniqueness construction uses the img R map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ImgRSuccAbove.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ImgRSuccAbove.lean#L26-L35

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

theorem GaussValuationUniqueness.imgR_map {R R' : Type*} [CommRing R] [CommRing R'] {D N : ℕ} (φ : R →+* R')
    (j0 : Fin (N + 1)) (ρ : Fin N → R) (t : TVar D N) :
    MvPolynomial.map φ (imgR j0 ρ t) = imgR j0 (fun k => φ (ρ k)) t := by sorry
