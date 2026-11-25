-- Prove2me | Theorems.Thm_GlobalTheory_ThetaLiftGL_compactOpen_basis
-- name    : GlobalTheory.ThetaLiftGL.compactOpen_basis
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:23.408553+00:00
-- url     : https://prove2.me/theorems/b4e67d6c-868a-442c-b13e-ce1d9718d8d9
-- title:
--   Theta Lift GL: compact Open basis
-- statement:
--   The Theta Lift GL construction uses the compact Open basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaCorrespondenceLargeRank.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaCorrespondenceLargeRank.lean#L18-L24

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

theorem GlobalTheory.ThetaLiftGL.compactOpen_basis (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
      IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by sorry
