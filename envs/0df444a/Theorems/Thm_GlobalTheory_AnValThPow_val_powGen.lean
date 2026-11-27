-- Prove2me | Theorems.Thm_GlobalTheory_AnValThPow_val_powGen
-- name    : GlobalTheory.AnValThPow.val_powGen
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-27T04:57:11.725238+00:00
-- url     : https://prove2.me/theorems/6b7d90c5-522f-49e5-bd33-99396f561b47
-- title:
--   An Val Th Pow: val pow Gen
-- statement:
--   The An Val Th Pow construction uses the val pow Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ThetaConstantPowEqOneOfPowerTrivial.lean#L110-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ThetaConstantPowEqOneOfPowerTrivial.lean#L110-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ThetaConstantPowEqOneOfPowerTrivial
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
open GlobalTheory GlobalTheory.AnValThPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S}

theorem GlobalTheory.AnValThPow.val_powGen (L : LB A.left) (k : ℤ) (θ : ThetaGrp A L k T) (n : ℕ) (q : Sp ℂ ⟶ (T ⊗ A).left)
    (j : Fin n × Fin 2 → L.ι) (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (powφ A θ.pt n) j) :
    valAt' q (LB.wchart L (powφ A θ.pt n) j) ((powGen A L k θ n).s j).val =
      ∏ i : Fin n, valAt' (q ≫ (translT A (θ.pt ^ (i : ℕ))).left)
        (LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] (fun b => j (i, b)))
        (θ.φ.s (fun b => j (i, b))).val := by sorry
