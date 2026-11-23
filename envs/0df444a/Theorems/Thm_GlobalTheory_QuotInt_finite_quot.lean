-- Prove2me | Theorems.Thm_GlobalTheory_QuotInt_finite_quot
-- name    : GlobalTheory.QuotInt.finite_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:54:49.621981+00:00
-- url     : https://prove2.me/theorems/7a3f9406-4b06-4242-a45a-3a52f5b9a4e9
-- title:
--   Quot Int: finite quot
-- statement:
--   The Quot Int construction uses the finite quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotientIntegralParabolicUnfolding.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotientIntegralParabolicUnfolding.lean#L64-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.QuotInt
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.QuotInt.finite_quot (K : Subgroup G) (hKo : IsOpen (K : Set G)) {C : Set G} (hC : IsCompact C) :
    ∃ S : Finset (G ⧸ K), ∀ g ∈ C, (g : G ⧸ K) ∈ S := by sorry
