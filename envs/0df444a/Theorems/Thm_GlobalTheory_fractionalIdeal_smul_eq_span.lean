-- Prove2me | Theorems.Thm_GlobalTheory_fractionalIdeal_smul_eq_span
-- name    : GlobalTheory.fractionalIdeal_smul_eq_span
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:54:09.282161+00:00
-- url     : https://prove2.me/theorems/15b23240-ebb8-4033-a871-773e3497c8e3
-- title:
--   Global Theory: fractional Ideal smul eq span
-- statement:
--   The Global Theory construction uses the fractional Ideal smul eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsPosNatMemFractionalIdeal.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsPosNatMemFractionalIdeal.lean#L23-L30

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsPosNatMemFractionalIdeal
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

theorem GlobalTheory.fractionalIdeal_smul_eq_span {E : Type} [Field E] [NumberField E] {r : ℕ}
    (a : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (L : Submodule (𝓞 E) (Fin r → E)) :
    (a : Submodule (𝓞 E) E) • L =
      Submodule.span (𝓞 E) {v | ∃ α ∈ a, ∃ u ∈ L, v = α • u} := by sorry
