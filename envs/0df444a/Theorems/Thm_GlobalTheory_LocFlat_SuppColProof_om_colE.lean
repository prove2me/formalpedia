-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_SuppColProof_om_colE
-- name    : GlobalTheory.LocFlat.SuppColProof.om_colE
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:20:32.771862+00:00
-- url     : https://prove2.me/theorems/85da65a2-57b5-44d3-ad31-be097e5175e6
-- title:
--   Supp Col Proof: om col E
-- statement:
--   The Supp Col Proof construction uses the om col E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnSupportOfOneIndexAtSymPosition.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnSupportOfOneIndexAtSymPosition.lean#L18-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnSupportOfOneIndexAtSymPosition
import Theorems.Thm_GlobalTheory_RootEx_Exchange_om_colE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.SuppColProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.LocFlat.SuppColProof.om_colE {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (μ : kˣ →* ℂˣ) (g h : GL (n ⊕ Fin c) k) (hg : Matrix.GeneralLinearGroup.det g = 1)
    (Φ : Matrix (n ⊕ Fin c) n' k → ℂ) :
    (fun z => om μ 1 h Φ (g.val * z)) = om μ 1 (g⁻¹ * h) Φ := by sorry
