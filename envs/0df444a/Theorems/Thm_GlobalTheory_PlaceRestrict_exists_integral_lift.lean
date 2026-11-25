-- Prove2me | Theorems.Thm_GlobalTheory_PlaceRestrict_exists_integral_lift
-- name    : GlobalTheory.PlaceRestrict.exists_integral_lift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:16:27.483819+00:00
-- url     : https://prove2.me/theorems/a259f37a-1f7a-50e9-a61f-b7dcab0048bc
-- title:
--   Place Restrict: exists integral lift
-- statement:
--   The Place Restrict construction uses the exists integral lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/PlacesRestrictInjective.lean#L79-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/PlacesRestrictInjective.lean#L79-L118

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.PlaceRestrict
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas

theorem GlobalTheory.PlaceRestrict.exists_integral_lift {Ω X : Type} [Field Ω] (S : Set X) (hS : S.Finite)
    (v : X → AddValuation Ω (WithTop ℤ)) (hinj : Set.InjOn v S)
    (hn : ∀ w ∈ S, IsNormDiscrete (v w)) (w : X) (hw : w ∈ S) (a : Ω) (ha : 0 ≤ v w a) :
    ∃ l : Ω, (∀ w' ∈ S, 0 ≤ v w' l) ∧ 0 < v w (a - l) := by sorry
