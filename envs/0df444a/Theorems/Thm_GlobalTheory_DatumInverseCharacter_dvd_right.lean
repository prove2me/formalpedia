-- Prove2me | Theorems.Thm_GlobalTheory_DatumInverseCharacter_dvd_right
-- name    : GlobalTheory.DatumInverseCharacter.dvd_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:41:57.254735+00:00
-- url     : https://prove2.me/theorems/a75278b0-b1ca-48f3-a97f-3a86fc3b4ab8
-- title:
--   Datum Inverse Character: dvd right
-- statement:
--   The Datum Inverse Character construction uses the dvd right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsQuotEquiv.lean#L36-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsQuotEquiv.lean#L36-L48

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsQuotEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DatumInverseCharacter
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.DatumInverseCharacter.dvd_right (D : Datum H) {N : ℕ} {I : Ideal (𝓞 E)}
    (hI : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)}) {c : 𝓞 E}
    (hc : c ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E)) (u : D.La) {w : D.La}
    (hw : w ∈ (I • ⊤ : Submodule (𝓞 E) D.La)) : (N : ℤ) ∣ D.EF u (c • w) := by sorry
