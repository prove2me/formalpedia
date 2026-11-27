-- Prove2me | Theorems.Thm_GlobalTheory_JetVal_isValueAt_jet
-- name    : GlobalTheory.JetVal.isValueAt_jet
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-27T04:48:18.592877+00:00
-- url     : https://prove2.me/theorems/bdf7aa93-f2b0-4a5d-8820-a592ee054e66
-- title:
--   Jet Val: is Value At jet
-- statement:
--   The Jet Val construction uses the is Value At jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsValueAtJetPointCmFrameSection.lean#L119-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsValueAtJetPointCmFrameSection.lean#L119-L212

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsValueAtJetPointCmFrameSection
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
open GlobalTheory GlobalTheory.JetVal
open AlgebraicGeometry CategoryTheory Opposite Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] (L : LB G.left) {x0 : Sp ℂ ⟶ X} {g : ℕ}
variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)) (hol : IsHolFam e) (he : ∀ z, e z ≫ G.hom = x0)

theorem GlobalTheory.JetVal.isValueAt_jet (holP : IsHolFam (lftJ e he)) (m k : ℕ)
    (F : LB.Sec (LPow G L (k : ℤ) (Over.mk x0)))
    (F' : LB.Sec (LPow G L (k : ℤ) (overAt x0 (Jet ℂ (Fin 1 × Fin g) m))))
    (hF' : IsPullSec G L (k : ℤ) (jB m ▷ G) (whiskerRight_snd _ _) F F')
    (θF : (Fin g → ℂ) → ℂ) (fr : L.ι → (Fin g → ℂ) → ℂ)
    (hfr : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j})
    (hfr0 : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0)
    (hrd : ∀ j z (pt : Sp ℂ ⟶ (Over.mk x0 ⊗ G).left), pt ≫ (snd (Over.mk x0) G).left = e z →
      pt ≫ (fst (Over.mk x0) G).left = 𝟙 (Sp ℂ) → ⊤ ≤ e z ⁻¹ᵁ L.U j →
      valAt' pt ((LPow G L (k : ℤ) (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θF z * fr j z ^ (k : ℤ))
    (τ : LB.Gen (LB.LinComb L (Y := (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) (K := Fin 1)
      (fun _ => (xJ e hol he m).left) (fun _ => (k : ℤ))))
    (hτ : ∀ (j : Fin 1 → L.ι) (h : ⊤ ≤ LB.wchart L (fun _ : Fin 1 => (xJ e hol he m).left) j),
      ((overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left.presheaf.map (homOfLE h).op).hom (τ.s j).val =
        toΓ _ (jetOf m (fun z => fr (j 0) z ^ k))) :
    IsValueAt G L (k : ℤ) F' (xJ e hol he m) τ (toΓ _ (jetOf m θF)) := by sorry
