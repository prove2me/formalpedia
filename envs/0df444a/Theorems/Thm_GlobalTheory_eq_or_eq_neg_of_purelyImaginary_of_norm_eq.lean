-- Prove2me | Theorems.Thm_GlobalTheory_eq_or_eq_neg_of_purelyImaginary_of_norm_eq
-- name    : GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:17:50.87602+00:00
-- url     : https://prove2.me/theorems/c8ad86d1-28a5-41fa-90cc-fd9e811961df
-- title:
--   Global Theory: eq or eq neg of purely Imaginary of norm eq
-- statement:
--   The Global Theory construction uses the eq or eq neg of purely Imaginary of norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqOrEqNegOfPurelyImaginaryOfNormEq.lean#L9-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqOrEqNegOfPurelyImaginaryOfNormEq.lean#L9-L23

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqOrEqNegOfPurelyImaginaryOfNormEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
open GlobalTheory

theorem GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ξ ξ' : E) (τ : E →+* ℂ),
      cc ξ = -ξ → cc ξ' = -ξ' → ‖τ ξ‖ = ‖τ ξ'‖ → ξ' = ξ ∨ ξ' = -ξ := by sorry
