-- Prove2me | Theorems.Thm_GlobalTheory_AnVal_JetAlg_anO_fr
-- name    : GlobalTheory.AnVal.JetAlg.anO_fr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:05.382652+00:00
-- url     : https://prove2.me/theorems/8d412b51-6daf-5537-8f75-3053762fc23e
-- title:
--   Jet Alg: an O fr
-- statement:
--   The Jet Alg construction uses the an O fr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetRdMulInvPow.lean#L128-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetRdMulInvPow.lean#L128-L139

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

theorem GlobalTheory.AnVal.JetAlg.anO_fr {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left} {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hψ : Φ.JetMap m ψ Λ) {j : L.L.ι} (hU : ⊤ ≤ ψ ⁻¹ᵁ L.L.U j) : AnO fun w => Φ.fr j (Λ w) := by sorry
