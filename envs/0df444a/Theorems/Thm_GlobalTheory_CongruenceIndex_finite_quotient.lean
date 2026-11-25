-- Prove2me | Theorems.Thm_GlobalTheory_CongruenceIndex_finite_quotient
-- name    : GlobalTheory.CongruenceIndex.finite_quotient
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:03:43.952399+00:00
-- url     : https://prove2.me/theorems/0b5e4f64-b5ac-4abe-9156-a6bd1bb60697
-- title:
--   Congruence Index: finite quotient
-- statement:
--   The Congruence Index construction uses the finite quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CongruenceFiniteIndex.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CongruenceFiniteIndex.lean#L97-L103

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

theorem GlobalTheory.CongruenceIndex.finite_quotient (hΛ : Λ.FG) {M : ℕ} (hM : 0 < M) :
    Finite (Λ ⧸ (nsmulAddMonoidHom M : Λ →+ Λ).range) := by sorry
