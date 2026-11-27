-- Prove2me | Theorems.Thm_GlobalTheory_AnValGenRd_exists_reading
-- name    : GlobalTheory.AnValGenRd.exists_reading
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-27T04:38:05.569835+00:00
-- url     : https://prove2.me/theorems/8d16306c-3aef-40b5-a400-a276f256f333
-- title:
--   An Val Gen Rd: exists reading
-- statement:
--   The An Val Gen Rd construction uses the exists reading property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsHolomorphicGeneratorReadingAutomorphy.lean#L170-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsHolomorphicGeneratorReadingAutomorphy.lean#L170-L219

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsHolomorphicGeneratorReadingAutomorphy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AnValGenRd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnValGenRd.exists_reading : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), t.IsGen → ∀ (N : ℕ) (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (p : K → (Fin N → ℂ) → Fin g → ℂ), IsHolFam q → (∀ k, Differentiable ℂ (p k)) → (∀ z k, q z ≫ φ k = (Φ.e (p k z)).left) → ∃ v : (Fin N → ℂ) → ℂ, Differentiable ℂ v ∧ (∀ z, v z ≠ 0) ∧ (∀ z, Φ.GenRd φ ε t (q z) (fun k => p k z) (v z)) ∧ (∀ z u, Φ.GenRd φ ε t (q z) (fun k => p k z) u → u = v z) ∧ ∀ z z' (a : K → Fin g → ℂ), q z' = q z → (∀ k, a k ∈ Φ.lat ∧ p k z' = p k z + a k) → v z' = v z * ∏ k, Φ.fac (a k) (p k z) ^ ε k := by sorry
