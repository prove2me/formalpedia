-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_PureColPf_coords_entry
-- name    : GlobalTheory.LocFlat.PureColPf.coords_entry
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:49.94357+00:00
-- url     : https://prove2.me/theorems/eb7810ac-4b20-4eb3-be5b-e8264fe203b5
-- title:
--   Pure Col Pf: coords entry
-- statement:
--   The Pure Col Pf construction uses the coords entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnIndicatorPureAtSymmetricPosition.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnIndicatorPureAtSymmetricPosition.lean#L27-L32

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
variable {k : Type} [Field k] {n n' ι ι' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

theorem GlobalTheory.LocFlat.PureColPf.coords_entry (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) (o' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (u : n ⊕ Fin c) (v : n' ⊕ Fin c') :
    (((typeFrame ϖ o).bas⁻¹).val * x * (typeFrame ϖ o').bas.val) u v =
      Sum.elim (fun _ => 1) (fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) u * x u v *
        Sum.elim (fun _ => 1) (fun i : Fin c' => (ϖ : k) ^ (i.val + 1)) v := by sorry
