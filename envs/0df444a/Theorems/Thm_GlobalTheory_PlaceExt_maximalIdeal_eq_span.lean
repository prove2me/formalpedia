-- Prove2me | Theorems.Thm_GlobalTheory_PlaceExt_maximalIdeal_eq_span
-- name    : GlobalTheory.PlaceExt.maximalIdeal_eq_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:29:51.102855+00:00
-- url     : https://prove2.me/theorems/2bbbd355-bc7d-4d33-9ce1-ea7a89bb9d91
-- title:
--   Place Ext: maximal Ideal eq span
-- statement:
--   The Place Ext construction uses the maximal Ideal eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L172-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L172-L177

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.PlaceExt
variable {R R' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R']
  [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
omit [IsLocalHom (algebraMap R R')]

theorem GlobalTheory.PlaceExt.maximalIdeal_eq_span
    (hmax : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalRing.maximalIdeal R' = Ideal.span {algebraMap R R' ϖ} := by sorry
