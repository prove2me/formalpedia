-- Prove2me | Theorems.Thm_GlobalTheory_FlagMahler_finite_bounded
-- name    : GlobalTheory.FlagMahler.finite_bounded
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:08:04.267769+00:00
-- url     : https://prove2.me/theorems/9bc94aa1-62cb-4daa-a15d-79a41bde00e9
-- title:
--   Flag Mahler: finite bounded
-- statement:
--   The Flag Mahler construction uses the finite bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MahlerCompactness.lean#L266-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MahlerCompactness.lean#L266-L287

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FlagMahler
open ReciprocityTheory.ChartRestriction.G.FD NumberField Module
open Matrix hiding col gram
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem GlobalTheory.FlagMahler.finite_bounded (B : X.Ψ → ℝ) :
    {α : E | IsIntegral ℤ ((X.den : E) * α) ∧ ∀ τ : X.Ψ, ‖τ.1 α‖ ≤ B τ}.Finite := by sorry
