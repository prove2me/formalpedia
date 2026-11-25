-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_ExchangeCol_phi_add_col
-- name    : GlobalTheory.SymChain.ExchangeCol.phi_add_col
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:10:56.715959+00:00
-- url     : https://prove2.me/theorems/10047213-64af-4c17-b577-5bce0ee3993e
-- title:
--   Exchange Col: phi add col
-- statement:
--   The Exchange Col construction uses the phi add col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixBlockColumnVanishingStep.lean#L37-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixBlockColumnVanishingStep.lean#L37-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixBlockColumnVanishingStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.ExchangeCol

theorem GlobalTheory.SymChain.ExchangeCol.phi_add_col (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (hP : S.Pattern t)
    (j c : ℕ) (H : j + c = s) (q : Fin c) (hρ : q.val + 1 ≤ S.ρ) (hc : q.val + 2 ≤ c)
    (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k)
    (hx : ∀ r, x (Sum.inl r) (Sum.inr q.succ) = 0) (w : XIx (Fin κ) t (j + 1) → k) :
    (S.T t).Phi j c H (x + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0) =
      if ∀ r, valuation k (((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r) < 1 then (S.T t).Phi j c H x else 0 := by sorry
