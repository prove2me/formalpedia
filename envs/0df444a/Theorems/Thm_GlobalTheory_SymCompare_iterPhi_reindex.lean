-- Prove2me | Theorems.Thm_GlobalTheory_SymCompare_iterPhi_reindex
-- name    : GlobalTheory.SymCompare.iterPhi_reindex
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:18:27.972839+00:00
-- url     : https://prove2.me/theorems/f98da09d-30bd-443e-a98b-d7efa29ae6b6
-- title:
--   Sym Compare: iter Phi reindex
-- statement:
--   The Sym Compare construction uses the iter Phi reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L221-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L221-L227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t t' : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype t'] [DecidableEq t']

theorem GlobalTheory.SymCompare.iterPhi_reindex (f : t ≃ t') (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ)
    (x : Matrix (Ix r t' (j + 1)) (Ix r t' j) k) :
    P.iterPhi t' μ hμ j x = P.iterPhi t μ hμ j (x.submatrix (eI r f (j + 1)) (eI r f j)) := by sorry
