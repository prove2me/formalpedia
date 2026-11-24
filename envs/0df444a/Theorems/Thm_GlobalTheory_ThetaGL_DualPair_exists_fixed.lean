-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGL_DualPair_exists_fixed
-- name    : GlobalTheory.ThetaGL.DualPair.exists_fixed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:22.739316+00:00
-- url     : https://prove2.me/theorems/42bcca15-ab7c-46e0-9c5b-e0c3d58002f1
-- title:
--   Dual Pair: exists fixed
-- statement:
--   The Dual Pair construction uses the exists fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaPairContragredientQuotient.lean#L49-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaPairContragredientQuotient.lean#L49-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairContragredientQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct
open GlobalTheory GlobalTheory.ThetaGL GlobalTheory.ThetaGL.DualPair
variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.ThetaGL.DualPair.exists_fixed (π : Representation ℂ G W) (hπ : IsSmooth π) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (w : W) :
    ∃ w' ∈ fixed π K, ∀ T : W →ₗ[ℂ] V, (∀ k ∈ K, ∀ x, T (π k x) = T x) → T w = T w' := by sorry
