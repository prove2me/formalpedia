-- Prove2me | Theorems.Thm_GlobalTheory_HermDen_exists_den
-- name    : GlobalTheory.HermDen.exists_den
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:19:07.626346+00:00
-- url     : https://prove2.me/theorems/2981f84f-d5f5-4d57-a495-3b8e7878b8c6
-- title:
--   Herm Den: exists den
-- statement:
--   The Herm Den construction uses the exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegralConj.lean#L17-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegralConj.lean#L17-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegralConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.HermDen
open ReciprocityTheory.ChartRestriction.G.FD

theorem GlobalTheory.HermDen.exists_den (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ den : 𝓞 E, den ≠ 0 ∧ ∀ x ∈ Λ, ∀ y ∈ Λ,
      IsIntegral ℤ ((den : E) * ReciprocityTheory.ChartRestriction.G.FD.herm G x y) := by sorry
