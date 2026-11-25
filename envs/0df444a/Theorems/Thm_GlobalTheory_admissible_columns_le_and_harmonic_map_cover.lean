-- Prove2me | Theorems.Thm_GlobalTheory_admissible_columns_le_and_harmonic_map_cover
-- name    : GlobalTheory.admissible_columns_le_and_harmonic_map_cover
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:26.195689+00:00
-- url     : https://prove2.me/theorems/ce274ba8-381f-4b4b-9a3a-b9832c9fe327
-- title:
--   Global Theory: admissible columns le and harmonic map cover
-- statement:
--   The Global Theory construction uses the admissible columns le and harmonic map cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AdmissibleColumnsLeAndHarmonicMapCover.lean#L95-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AdmissibleColumnsLeAndHarmonicMapCover.lean#L95-L108

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AdmissibleColumnsLeAndHarmonicMapCover
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
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.admissible_columns_le_and_harmonic_map_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), (∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → Dw.p + Dw.q ≤ n) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by sorry
