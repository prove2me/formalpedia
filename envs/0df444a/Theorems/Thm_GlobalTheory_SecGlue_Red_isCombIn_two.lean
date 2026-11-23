-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Red_isCombIn_two
-- name    : GlobalTheory.SecGlue.Red.isCombIn_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:31:01.41223+00:00
-- url     : https://prove2.me/theorems/2cec9a53-394f-40d2-a35e-db86dec029a8
-- title:
--   Red: is Comb In two
-- statement:
--   The Red construction uses the is Comb In two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowCocycle.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowCocycle.lean#L62-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgHomEqMulPowOfEqLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Red

theorem GlobalTheory.SecGlue.Red.isCombIn_two {Y : Scheme.{0}} {V : Y.Opens} {S : Type} [CommRing S] {u c w₀ w₁ : Sp S ⟶ Y}
    {a₀ a₁ : S} (h : IsCombIn V u c ![w₀, w₁] ![a₀, a₁]) :
    ∃ (hu : u ⁻¹ᵁ V = ⊤) (hc : c ⁻¹ᵁ V = ⊤) (hw₀ : w₀ ⁻¹ᵁ V = ⊤) (hw₁ : w₁ ⁻¹ᵁ V = ⊤),
      ∀ x, chartHom V c hc x = chartHom V u hu x + a₀ * (chartHom V w₀ hw₀ x - chartHom V u hu x)
        + a₁ * (chartHom V w₁ hw₁ x - chartHom V u hu x) := by sorry
