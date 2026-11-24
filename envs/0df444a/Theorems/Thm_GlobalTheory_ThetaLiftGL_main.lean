-- Prove2me | Theorems.Thm_GlobalTheory_ThetaLiftGL_main
-- name    : GlobalTheory.ThetaLiftGL.main
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:42:55.728809+00:00
-- url     : https://prove2.me/theorems/b494bbb1-093d-4f2b-9370-a3a83820f26b
-- title:
--   Theta Lift GL: main
-- statement:
--   The Theta Lift GL construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaCorrespondenceLargeRank.lean#L26-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaCorrespondenceLargeRank.lean#L26-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisGeometry__HoweDualityGL_c4f3064dc8a43034
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairContragredientQuotientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwistStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaCorrespondenceLargeRank
import Theorems.Thm_GlobalTheory_PowerTwoNormLowerBound_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published
open scoped TensorProduct
open GlobalTheory GlobalTheory.ThetaLiftGL

theorem GlobalTheory.ThetaLiftGL.main : BernsteinZelevinskyFiniteness → BernsteinUnitaryProductIrreducible → HoweDualityGL →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ)
    (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W), r < t →
    IsSmoothChar μ → IsUnitaryChar μ → IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → IsSmooth π →
    π.IsIrreducible → ThetaPair μ σ π → Nonempty (π.Equiv (prod₂ σ (detRep (Fin t) μ))) := by sorry
