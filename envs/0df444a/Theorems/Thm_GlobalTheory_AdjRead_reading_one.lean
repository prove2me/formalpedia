-- Prove2me | Theorems.Thm_GlobalTheory_AdjRead_reading_one
-- name    : GlobalTheory.AdjRead.reading_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-27T05:31:08.552523+00:00
-- url     : https://prove2.me/theorems/e729f94e-a4ca-490e-b742-e9bfc739088e
-- title:
--   Adj Read: reading one
-- statement:
--   The Adj Read construction uses the reading one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsAdjReadingOne.lean#L220-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsAdjReadingOne.lean#L220-L329

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGenRosati
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigidStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsAdjReadingOne
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
open GlobalTheory GlobalTheory.AdjRead
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
variable {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem GlobalTheory.AdjRead.reading_one (f f' : A ⟶ A) [IsMonHom f] [IsMonHom f']
    (H : LBIso (cubeLB A ![fst A A ≫ f, snd A A] L.L) (cubeLB A ![fst A A, snd A A ≫ f'] L.L))
    (α β : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hα : ∀ z, Φ.e (α z) = Φ.e z ≫ f) (hβ : ∀ z, Φ.e (β z) = Φ.e z ≫ f')
    (h₁ : ∀ z w, hermForm Φ.Hm (α z) w = hermForm Φ.Hm z (β w))
    (h₂ : ∀ z w, hermForm Φ.Hm (β z) w = hermForm Φ.Hm z (α w)) :
    ∃ u : LB.Gen (LB.LinComb L.L (adφ f f') adε), u.IsGen ∧ ∀ z w : Fin g → ℂ,
      Φ.GenRd _ _ u (lift (Φ.e z) (Φ.e w)).left
        (Sum.elim (fun I => psumL 2 g I ![z, β w]) (fun I => psumL 2 g I ![α z, w])) 1 := by sorry
