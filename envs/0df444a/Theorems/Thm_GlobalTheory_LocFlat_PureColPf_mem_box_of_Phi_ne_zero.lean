-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_PureColPf_mem_box_of_Phi_ne_zero
-- name    : GlobalTheory.LocFlat.PureColPf.mem_box_of_Phi_ne_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:15.426703+00:00
-- url     : https://prove2.me/theorems/2fafa204-a823-5cac-a7fc-b42f66fef185
-- title:
--   Pure Col Pf: mem box of Phi ne zero
-- statement:
--   The Pure Col Pf construction uses the mem box of Phi ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnIndicatorPureAtSymmetricPosition.lean#L124-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnIndicatorPureAtSymmetricPosition.lean#L124-L179

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnIndicatorPureAtSymmetricPosition
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
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.PureColPf
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem GlobalTheory.LocFlat.PureColPf.mem_box_of_Phi_ne_zero (hpat : S.Pattern t) (j c : ℕ) (H : j + 1 + c = s) (r : ℕ) (hr : c + 1 = 2 * r)
    (z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k)
    (hz : ∀ a, z (.inl a) (.inr ⟨r, by omega⟩) = 0) (y : XIx (Fin κ) t (j + 1) → k)
    (h : (S.T t).Phi j (c + 1) (by omega) (z + colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y) ≠ 0) :
    y ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ r)⁻¹ := by sorry
