-- Prove2me | Theorems.Thm_GlobalTheory_AnVal_JetAlg_anO_prod
-- name    : GlobalTheory.AnVal.JetAlg.anO_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:05.347186+00:00
-- url     : https://prove2.me/theorems/8eba243b-ebf3-5a6b-b924-1bdf1b0a6173
-- title:
--   Jet Alg: an O prod
-- statement:
--   The Jet Alg construction uses the an O prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetRdMulInvPow.lean#L144-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetRdMulInvPow.lean#L144-L163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetAlg
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {n m : ℕ}
variable {K : Type} [Fintype K] {φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)}
  {Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}

theorem GlobalTheory.AnVal.JetAlg.anO_prod (hφ : ∀ k, Φ.JetMap m (φ k) (Λ k)) (ε : K → ℤ) {j : K → L.L.ι} (h : ⊤ ≤ LB.wchart L.L φ j) :
    AnO fun w => ∏ k, Φ.fr (j k) (Λ k w) ^ ε k := by sorry
