-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_IdealPow_ipow_sum_le
-- name    : GlobalTheory.DegCnt.IdealPow.ipow_sum_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:00.780816+00:00
-- url     : https://prove2.me/theorems/3d11afa3-0d66-5086-946d-85853e110332
-- title:
--   Ideal Pow: ipow sum le
-- statement:
--   The Ideal Pow construction uses the ipow sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemOfForall.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemOfForall.lean#L57-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemOfForall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.IdealPow
variable {K : Type} [Field K] [NumberField K] {𝔡 : Ideal (𝓞 K)}

theorem GlobalTheory.DegCnt.IdealPow.ipow_sum_le (h : 𝔡 ≠ ⊥) {ι : Type} [Fintype ι] (n : ι → ℤ) (J : Submodule (𝓞 K) K)
    (hJ : ∀ α : ι → K, (∀ i, α i ∈ ipow 𝔡 (n i)) → ∏ i, α i ∈ J) : ipow 𝔡 (∑ i, n i) ≤ J := by sorry
