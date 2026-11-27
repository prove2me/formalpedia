-- Prove2me | Theorems.Thm_GlobalTheory_AnVal_filter_col_toMultiset
-- name    : GlobalTheory.AnVal.filter_col_toMultiset
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T04:39:43.965087+00:00
-- url     : https://prove2.me/theorems/bdc430e3-5443-593b-9384-3a9f9bf8fae5
-- title:
--   An Val: filter col to Multiset
-- statement:
--   The An Val construction uses the filter col to Multiset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PolyDerivProdColumnFunctions.lean#L17-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PolyDerivProdColumnFunctions.lean#L17-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PolyDerivProdColumnFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal
open scoped ContDiff

theorem GlobalTheory.AnVal.filter_col_toMultiset {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ}
    (m : Formalism.L2.Pj.Letter T r n →₀ ℕ) (b : Fin n) :
    (Finsupp.toMultiset m).filter (fun ℓ => ℓ.2.2 = b) =
      (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm
        fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, b⟩)).map
        (fun ℓ : (Σ τ : T, Fin (r τ)) => (⟨ℓ.1, ℓ.2, b⟩ : Formalism.L2.Pj.Letter T r n)) := by sorry
