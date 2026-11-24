-- Prove2me | Theorems.Thm_GlobalTheory_FinCovol_compactSpace_unitary_of_definite
-- name    : GlobalTheory.FinCovol.compactSpace_unitary_of_definite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:24:27.282839+00:00
-- url     : https://prove2.me/theorems/c2ca922b-6dbd-4284-9f8e-337f06ed271a
-- title:
--   Fin Covol: compact Space unitary of definite
-- statement:
--   The Fin Covol construction uses the compact Space unitary of definite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/CompactSpaceRealUnitaryGroupOfDefinite.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/CompactSpaceRealUnitaryGroupOfDefinite.lean#L15-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsCompactOrthBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OrthonormalFramesBoundedOfDefinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CompactSpaceRealUnitaryGroupOfDefinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.FinCovol
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.FinCovol.compactSpace_unitary_of_definite :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)),
      (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) →
      (X.p0 = 0 ∨ X.p0 = r) → CompactSpace H) := by sorry
