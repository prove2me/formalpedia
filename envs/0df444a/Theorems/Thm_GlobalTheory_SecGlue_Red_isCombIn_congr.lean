-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Red_isCombIn_congr
-- name    : GlobalTheory.SecGlue.Red.isCombIn_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:30:28.898801+00:00
-- url     : https://prove2.me/theorems/3a1e4df8-0ba1-4f0f-8606-441dc9333860
-- title:
--   Red: is Comb In congr
-- statement:
--   The Red construction uses the is Comb In congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowCocycle.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowCocycle.lean#L51-L54

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

theorem GlobalTheory.SecGlue.Red.isCombIn_congr {Y : Scheme.{0}} {V : Y.Opens} {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    {u u' c c' : Sp S ⟶ Y} {w w' : ι → (Sp S ⟶ Y)} {a a' : ι → S} (hu : u = u') (hc : c = c')
    (hw : w = w') (ha : a = a') (h : IsCombIn V u c w a) : IsCombIn V u' c' w' a' := by sorry
