-- Prove2me | Theorems.Thm_GlobalTheory_T_integralClosure_finite_local_complete_mixedChar
-- name    : GlobalTheory.T.integralClosure_finite_local_complete_mixedChar
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:23:31.43515+00:00
-- url     : https://prove2.me/theorems/6b28f5e6-7067-45c4-8efa-e1222a571dc7
-- title:
--   T: integral Closure finite local complete mixed Char
-- statement:
--   The T construction uses the integral Closure finite local complete mixed Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralClosureFiniteLocalCompleteMixedCharStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IntegralClosureFiniteLocalCompleteMixedCharStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralClosureFiniteLocalCompleteMixedChar
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_BetaAtSymm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralClosureFiniteLocalCompleteMixedCharStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.integralClosure_finite_local_complete_mixedChar : ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S] (p : ℕ), p.Prime → (p : S) ∈ maximalIdeal S → IsNoetherianRing S → IsAdicComplete (maximalIdeal S) S → Module.Finite S (integralClosure S (FractionRing S)) ∧ ∃ _ : IsLocalRing (integralClosure S (FractionRing S)), IsNoetherianRing (integralClosure S (FractionRing S)) ∧ IsAdicComplete (maximalIdeal (integralClosure S (FractionRing S))) (integralClosure S (FractionRing S)) := by sorry
