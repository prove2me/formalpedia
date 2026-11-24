-- Prove2me | Theorems.Thm_GlobalTheory_HtVal_dvr_val
-- name    : GlobalTheory.HtVal.dvr_val
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:03:26.628877+00:00
-- url     : https://prove2.me/theorems/1bcad535-df63-4217-b045-a15f3bf84444
-- title:
--   Ht Val: dvr val
-- statement:
--   The Ht Val construction uses the dvr val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHeightOneValuationsControlSubgroup.lean#L10-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHeightOneValuationsControlSubgroup.lean#L10-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_MemRangeOfForallHeightOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationAtPrimeIsDiscreteValuationRingOfHeig
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHeightOneValuationsControlSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HtVal

theorem GlobalTheory.HtVal.dvr_val (S : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] (K : Type) [Field K]
    [Algebra S K] [IsFractionRing S K] :
    ∃ w : Kˣ →* Multiplicative ℤ, ∀ x : Kˣ,
      0 ≤ Multiplicative.toAdd (w x) ↔ (x : K) ∈ (algebraMap S K).range := by sorry
