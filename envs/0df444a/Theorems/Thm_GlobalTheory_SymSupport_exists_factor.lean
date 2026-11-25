-- Prove2me | Theorems.Thm_GlobalTheory_SymSupport_exists_factor
-- name    : GlobalTheory.SymSupport.exists_factor
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:24.94981+00:00
-- url     : https://prove2.me/theorems/bcedb848-5456-42bf-bebe-1fcd83c8cda0
-- title:
--   Sym Support: exists factor
-- statement:
--   The Sym Support construction uses the exists factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainSupportOneOfPattern.lean#L81-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainSupportOneOfPattern.lean#L81-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
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
open GlobalTheory GlobalTheory.SymSupport
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.SymSupport.exists_factor {g : GL (n ⊕ Fin c) k} (hg : g ∈ KO k _) (T : n → Prop)
    (h1 : ∀ l s, T s → valuation k (g.val (.inr l) (.inl s)) < 1)
    (h2 : ∀ r i, lev 1 (Sum.inr i : n ⊕ Fin c) ≤ lev 1 r →
      valuation k (g.val r (.inr i) - (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i)) < 1) :
    ∃ r : GL (n ⊕ Fin c) k, InR r.val ∧ ∃ D : Matrix (Fin c) n k, IntM D ∧ (∀ l s, T s → D l s = 0) ∧
      ∃ u ∈ KOne k (n ⊕ Fin c), g = r * lowU D * u := by sorry
