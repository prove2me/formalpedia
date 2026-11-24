-- Prove2me | Theorems.Thm_GlobalTheory_OpenImmDim_topologicalKrullDim_eq_of_isOpenImmersion
-- name    : GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:18:27.889344+00:00
-- url     : https://prove2.me/theorems/89ea733e-c89b-4430-8f9e-97d1f2b4c2b3
-- title:
--   Open Imm Dim: topological Krull Dim eq of is Open Immersion
-- statement:
--   The Open Imm Dim construction uses the topological Krull Dim eq of is Open Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimEqOfOpenImmersionIntegralSche.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimEqOfOpenImmersionIntegralSche.lean#L9-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfIsIsoRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfOpenImmersionIntegralSche
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.OpenImmDim

theorem GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion : ∀ (F : Type) [Field F] (X V : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp F) (ℓ : V ⟶ X) [LocallyOfFiniteType p] [IsOpenImmersion ℓ]
    [Nonempty V], topologicalKrullDim V = topologicalKrullDim X := by sorry
