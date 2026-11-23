-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_smul_map_mulVec_pi
-- name    : GlobalTheory.WeilM.smul_map_mulVec_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:50.328121+00:00
-- url     : https://prove2.me/theorems/7b6d7db1-d908-46f9-989f-93821af9ab7b
-- title:
--   Weil M: smul map mul Vec pi
-- statement:
--   The Weil M construction uses the smul map mul Vec pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsLocallyConstantAddChar.lean#L105-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsLocallyConstantAddChar.lean#L105-L146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormPowTwoPowSubOneGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Pointwise
open GlobalTheory GlobalTheory.WeilM
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F} [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]

theorem GlobalTheory.WeilM.smul_map_mulVec_pi (M : Matrix κ κ F) (u : Fˣ) (hu : (u : F) = M.det) :
    (distribHaarChar F u : ENNReal) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν) = Measure.pi fun _ : κ => ν := by sorry
