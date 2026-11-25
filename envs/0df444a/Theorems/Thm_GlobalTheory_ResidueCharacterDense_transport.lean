-- Prove2me | Theorems.Thm_GlobalTheory_ResidueCharacterDense_transport
-- name    : GlobalTheory.ResidueCharacterDense.transport
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:29:38.155599+00:00
-- url     : https://prove2.me/theorems/504d589f-0131-5603-a75b-4d4580bfa877
-- title:
--   Residue Character Dense: transport
-- statement:
--   The Residue Character Dense construction uses the transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L106-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L106-L113

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense

theorem GlobalTheory.ResidueCharacterDense.transport (r l : ℕ) [Fact r.Prime] [Fact l.Prime] (h : r = l) (K : Type) [Field K]
    [TopologicalSpace K] [Algebra ℚ_[r] K] (hc : Continuous (algebraMap ℚ_[r] K))
    (hf : FiniteDimensional ℚ_[r] K) :
    ∃ _ : Algebra ℚ_[l] K, Continuous (algebraMap ℚ_[l] K) ∧ FiniteDimensional ℚ_[l] K ∧
      ∀ (z : K) (a : ℚ), ‖Algebra.trace ℚ_[r] K z - (a : ℚ_[r])‖ =
        ‖Algebra.trace ℚ_[l] K z - (a : ℚ_[l])‖ := by sorry
