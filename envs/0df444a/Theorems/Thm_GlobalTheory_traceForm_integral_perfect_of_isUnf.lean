-- Prove2me | Theorems.Thm_GlobalTheory_traceForm_integral_perfect_of_isUnf
-- name    : GlobalTheory.traceForm_integral_perfect_of_isUnf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:08.238178+00:00
-- url     : https://prove2.me/theorems/bbbf9456-02d8-4752-bdba-7c8c0a891a17
-- title:
--   Global Theory: trace Form integral perfect of is Unf
-- statement:
--   The Global Theory construction uses the trace Form integral perfect of is Unf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/TraceFormIntegralPerfectOfIsUnf.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/TraceFormIntegralPerfectOfIsUnf.lean#L9-L21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_TraceFormIntegralPerfectOfIsUnf
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

theorem GlobalTheory.traceForm_integral_perfect_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ k, (∀ x ∈ (U.X k).Λ, ∀ y ∈ (U.X k).Λ, ∃ n : ℤ, EFf (U.X k).ξ0 (U.X k).Gm x y = n) ∧ ∀ φ : (U.X k).Λ →+ ℤ, ∃ x ∈ (U.X k).Λ, ∀ y : (U.X k).Λ, (φ y : ℚ) = EFf (U.X k).ξ0 (U.X k).Gm x y := by sorry
