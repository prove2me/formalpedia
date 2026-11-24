-- Prove2me | Theorems.Thm_GlobalTheory_NormMod_exists_norm_mod_mul
-- name    : GlobalTheory.NormMod.exists_norm_mod_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:36:37.620047+00:00
-- url     : https://prove2.me/theorems/9e92dbe1-b8d3-4d20-a55a-7ddafb63dcd0
-- title:
--   Norm Mod: exists norm mod mul
-- statement:
--   The Norm Mod construction uses the exists norm mod mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsHostNormModCoprimeLevelHalf.lean#L275-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsHostNormModCoprimeLevelHalf.lean#L275-L289

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormMod
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HostModel
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem GlobalTheory.NormMod.exists_norm_mod_mul {k : ℕ} (hk : k ≠ 0) {ν : ℤ} (hν : IsCoprime ν (k : ℤ)) :
    ∀ {m : ℕ}, m ≠ 0 → ∀ {t : 𝓞 E}, (m : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) →
      ∃ s : 𝓞 E, ((m * k : ℕ) : 𝓞 E) ∣ s * H.bar s - (ν : 𝓞 E) ∧ (m : 𝓞 E) ∣ s - t := by sorry
