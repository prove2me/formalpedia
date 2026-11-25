-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigmaL_mem_relSpan
-- name    : GroundTheory.Automorphic.Whittaker.sigmaL_mem_relSpan
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:07.560877+00:00
-- url     : https://prove2.me/theorems/fc122233-3d41-4f95-a826-2e6be977d964
-- title:
--   Whittaker: sigma L mem rel Span
-- statement:
--   The Whittaker construction uses the sigma L mem rel Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L114-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L114-L121

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

theorem GroundTheory.Automorphic.Whittaker.sigmaL_mem_relSpan {U : Set (GL (Fin n) F)} {r : GL (Fin n) F → ℂ}
    (hr : r ∈ relSpan (chi (n := n) ψ₀) U) : sigmaL r ∈ relSpan (chi (n := n) ψ₀) (sigma ⁻¹' U) := by sorry
