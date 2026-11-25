-- Prove2me | Theorems.Thm_GlobalTheory_Published_finitenessOfHermitianClasses_holds
-- name    : GlobalTheory.Published.finitenessOfHermitianClasses_holds
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:36.611671+00:00
-- url     : https://prove2.me/theorems/1ad80f06-ffe6-443f-8820-63e9b70307c0
-- title:
--   Published: finiteness Of Hermitian Classes holds
-- statement:
--   The Published construction uses the finiteness Of Hermitian Classes holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteUnitaryClassesOfDualEqSmul.lean#L123-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteUnitaryClassesOfDualEqSmul.lean#L123-L131

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteRepresentatives_c0b95eec68dc9003
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteUnitaryClassesOfDualEqSmul_87ddafdad67ddc06
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.MultiplicativeHeights
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.Published.finitenessOfHermitianClasses_holds : Published.FinitenessOfHermitianClasses := by sorry
