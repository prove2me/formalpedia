-- Prove2me | Theorems.Thm_GlobalTheory_HeightInv_relIndex_span_map
-- name    : GlobalTheory.HeightInv.relIndex_span_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:55.298943+00:00
-- url     : https://prove2.me/theorems/812e14e6-2184-4957-a945-94d19ac572b6
-- title:
--   Height Inv: rel Index span map
-- statement:
--   The Height Inv construction uses the rel Index span map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RelIndexSpanMap.lean#L14-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RelIndexSpanMap.lean#L14-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.HeightInv
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

theorem GlobalTheory.HeightInv.relIndex_span_map {R K V ι : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V]
    [Module K V] [Module R V] [IsScalarTower R K V] (Λ : Submodule R V) (f : V →ₗ[K] V)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) (hΛ : ∀ x, x ∈ Λ ↔ f x ∈ Λ)
    (w : ι → V) :
    (Submodule.span R (Set.range fun a => f (w a))).toAddSubgroup.relIndex
        (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range fun a => f (w a))).toAddSubgroup) =
      (Submodule.span R (Set.range w)).toAddSubgroup.relIndex
        (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup) := by sorry
