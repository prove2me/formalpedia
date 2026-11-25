-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_relSpan_mono
-- name    : GroundTheory.Automorphic.Whittaker.relSpan_mono
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:57:51.111803+00:00
-- url     : https://prove2.me/theorems/16728c8e-d138-4d6c-871c-cb85e5154203
-- title:
--   Whittaker: rel Span mono
-- statement:
--   The Whittaker construction uses the rel Span mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L108-L112

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [TopologicalSpace F] [IsTopologicalRing F]
variable (ψ₀ : AddChar F ℂ)

theorem GroundTheory.Automorphic.Whittaker.relSpan_mono {χ : NN F n →* ℂ} {U V : Set (GL (Fin n) F)} (hUV : U ⊆ V) :
    relSpan χ U ≤ relSpan χ V := by sorry
