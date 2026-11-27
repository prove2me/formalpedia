-- Prove2me | Theorems.Thm_GlobalTheory_T_polyDeriv_prod_column_functions
-- name    : GlobalTheory.T.polyDeriv_prod_column_functions
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T04:45:20.091897+00:00
-- url     : https://prove2.me/theorems/3f37ff38-1a95-48b6-8462-5708b8c7db54
-- title:
--   T: poly Deriv prod column functions
-- statement:
--   The T construction uses the poly Deriv prod column functions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PolyDerivProdColumnFunctionsStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PolyDerivProdColumnFunctionsStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PolyDerivProdColumnFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PolyDerivProdColumnFunctionsStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.polyDeriv_prod_column_functions : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (T : Type) [Fintype T] (r : T → ℕ) (n : ℕ) (u : (Σ τ : T, Fin (r τ)) → V) (θ : Fin n → V → ℂ), (∀ b, Differentiable ℂ (θ b)) → ∀ P : MvPolynomial (Formalism.L2.Pj.Letter T r n) ℂ, I2.polyDeriv P (fun ℓ => (Pi.single ℓ.2.2 (u ⟨ℓ.1, ℓ.2.1⟩) : Fin n → V)) (fun z => ∏ b, θ b (z b)) 0 = ∑ m ∈ P.support, P.coeff m * ∏ b, I2.polyDeriv (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, b⟩) (1 : ℂ)) u (θ b) 0 := by sorry
