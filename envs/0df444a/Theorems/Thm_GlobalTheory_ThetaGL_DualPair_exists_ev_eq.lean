-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGL_DualPair_exists_ev_eq
-- name    : GlobalTheory.ThetaGL.DualPair.exists_ev_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:25.9008+00:00
-- url     : https://prove2.me/theorems/9a0954ee-5124-446f-b536-698e0ce231d4
-- title:
--   Dual Pair: exists ev eq
-- statement:
--   The Dual Pair construction uses the exists ev eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaPairContragredientQuotient.lean#L97-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaPairContragredientQuotient.lean#L97-L121

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

theorem GlobalTheory.ThetaGL.DualPair.exists_ev_eq (π : Representation ℂ G W) (hπ : IsAdmissible π) (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (T : W →ₗ[ℂ] V)
    (hT : ∀ k ∈ K, ∀ x, T (π k x) = T x) : ∃ t, ev V π t = T := by sorry
