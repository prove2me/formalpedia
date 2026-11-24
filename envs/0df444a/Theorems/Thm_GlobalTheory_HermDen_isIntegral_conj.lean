-- Prove2me | Theorems.Thm_GlobalTheory_HermDen_isIntegral_conj
-- name    : GlobalTheory.HermDen.isIntegral_conj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:19:09.815948+00:00
-- url     : https://prove2.me/theorems/f098cc73-4dc8-490c-b686-4820dacc2acc
-- title:
--   Herm Den: is Integral conj
-- statement:
--   The Herm Den construction uses the is Integral conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegralConj.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegralConj.lean#L13-L15

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

theorem GlobalTheory.HermDen.isIntegral_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {x : E}
    (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) := by sorry
