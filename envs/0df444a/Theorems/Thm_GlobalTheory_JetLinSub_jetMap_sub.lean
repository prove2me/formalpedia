-- Prove2me | Theorems.Thm_GlobalTheory_JetLinSub_jetMap_sub
-- name    : GlobalTheory.JetLinSub.jetMap_sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T18:43:33.448217+00:00
-- url     : https://prove2.me/theorems/536153f7-eb28-51eb-9574-30d8f878667b
-- title:
--   Jet Lin Sub: jet Map sub
-- statement:
--   The Jet Lin Sub construction uses the jet Map sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetReadingLinearSubstitutionPoints.lean#L163-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetReadingLinearSubstitutionPoints.lean#L163-L178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
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
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetLinSub
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem GlobalTheory.JetLinSub.jetMap_sub {n n' m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : Φ.JetMap m ψ Λ) :
    Φ.JetMap m (spMap (σ : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ ψ) (Λ ∘ₗ B) := by sorry
