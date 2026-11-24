-- Prove2me | Theorems.Thm_GlobalTheory_ConvexCutOff_exists_support
-- name    : GlobalTheory.ConvexCutOff.exists_support
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:32.838799+00:00
-- url     : https://prove2.me/theorems/f4a1e243-3067-43c7-a0d7-aefae5c89d72
-- title:
--   Convex Cut Off: exists support
-- statement:
--   The Convex Cut Off construction uses the exists support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolyDerivRenameOfConvex.lean#L9-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolyDerivRenameOfConvex.lean#L9-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPermOfOfFnPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolyDerivRenameOfConvex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory GlobalTheory.ConvexCutOff

theorem GlobalTheory.ConvexCutOff.exists_support {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {K : Set V} (hK : Convex ℝ K) (hne : K.Nonempty) {x : V} (hx : x ∉ interior K) :
    ∃ f : V →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ K, f y ≤ f x := by sorry
