-- Prove2me | Theorems.Thm_GlobalTheory_T_section_reading_existsUnique_isTheta
-- name    : GlobalTheory.T.section_reading_existsUnique_isTheta
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:20.21431+00:00
-- url     : https://prove2.me/theorems/4bb83819-0d74-4c5d-9dd4-a55072154f99
-- title:
--   T: section reading exists Unique is Theta
-- statement:
--   The T construction uses the section reading exists Unique is Theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/SectionReadingExistsUniqueIsThetaStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/SectionReadingExistsUniqueIsThetaStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SectionReadingExistsUniqueIsTheta
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SectionReadingExistsUniqueIsThetaStatement
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

theorem GlobalTheory.T.section_reading_existsUnique_isTheta : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))), (∃! θ, Φ.Rd k F θ) ∧ (∀ θ, Φ.Rd k F θ → Φ.IsTh k θ) ∧ ∀ θ, Φ.Rd k F θ ↔ ∀ z, ∃ j, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j ∧ valAt' (ptSecT A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θ z * Φ.fr j z ^ k := by sorry
