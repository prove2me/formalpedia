-- Prove2me | Theorems.Thm_GlobalTheory_QuotInt_exists_open_stab
-- name    : GlobalTheory.QuotInt.exists_open_stab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:54:32.613541+00:00
-- url     : https://prove2.me/theorems/54e105b1-7322-4d23-941a-55b1f3599e3e
-- title:
--   Quot Int: exists open stab
-- statement:
--   The Quot Int construction uses the exists open stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotientIntegralParabolicUnfolding.lean#L17-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotientIntegralParabolicUnfolding.lean#L17-L50

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

theorem GlobalTheory.QuotInt.exists_open_stab {F : G → ℂ} (hF : F ∈ SB G) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g, ∀ x ∈ K, F (g * x) = F g := by sorry
