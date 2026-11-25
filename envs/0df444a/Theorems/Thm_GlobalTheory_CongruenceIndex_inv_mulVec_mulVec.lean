-- Prove2me | Theorems.Thm_GlobalTheory_CongruenceIndex_inv_mulVec_mulVec
-- name    : GlobalTheory.CongruenceIndex.inv_mulVec_mulVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:42.00484+00:00
-- url     : https://prove2.me/theorems/064c16b8-3535-4f38-9184-5aba171c76ed
-- title:
--   Congruence Index: inv mul Vec mul Vec
-- statement:
--   The Congruence Index construction uses the inv mul Vec mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CongruenceFiniteIndex.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CongruenceFiniteIndex.lean#L35-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CongruenceFiniteIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CongruenceIndex
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.CongruenceIndex.inv_mulVec_mulVec (γ : GL (Fin r) E) (v : Fin r → E) :
    ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)
      = v := by sorry
