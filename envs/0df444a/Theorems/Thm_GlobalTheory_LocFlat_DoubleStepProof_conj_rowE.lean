-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_DoubleStepProof_conj_rowE
-- name    : GlobalTheory.LocFlat.DoubleStepProof.conj_rowE
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:33:38.161095+00:00
-- url     : https://prove2.me/theorems/3266bcbc-198a-4f27-86b9-0660c0043c8c
-- title:
--   Double Step Proof: conj row E
-- statement:
--   The Double Step Proof construction uses the conj row E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymLevelDoubleStepOfFlatColumnFlatRow.lean#L135-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymLevelDoubleStepOfFlatColumnFlatRow.lean#L135-L168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRow
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
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.DoubleStepProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem GlobalTheory.LocFlat.DoubleStepProof.conj_rowE (j c : ℕ) (H : j + 1 + (c + 1) = s) (r : ℕ) (v : XIx (Fin κ) t (j + 1) → k) :
    ((typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1 + 1) (by omega))).conj.symm
      (rowE (c + 1 + 1) (r + 1) v)).val =
      (fromBlocks 1 0 (Matrix.of fun (l : Fin (c + 1 + 1)) x => if l.val = r then (((S.ϖ : k) ^ (r + 1))⁻¹ * v x) else 0) 1 :
        Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k).submatrix
        (stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1 + 1) (by omega))
        (stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1 + 1) (by omega)) := by sorry
