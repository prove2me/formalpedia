-- Prove2me | Theorems.Thm_GlobalTheory_SymSupportP_exists_factor
-- name    : GlobalTheory.SymSupportP.exists_factor
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:29:50.050317+00:00
-- url     : https://prove2.me/theorems/77b16a43-7d5a-54b9-b868-597be6950b12
-- title:
--   Sym Support P: exists factor
-- statement:
--   The Sym Support P construction uses the exists factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainSupportAtOfPattern.lean#L15-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainSupportAtOfPattern.lean#L15-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRootExchangeParabolicMulPrincipalCongruencStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainSupportAtOfPattern
import Theorems.Thm_GlobalTheory_SymSupport_exists_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymSupport
noncomputable section
open GlobalTheory GlobalTheory.SymSupportP
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.SymSupportP.exists_factor {g : GL (n ⊕ Fin c) k} (hg : g ∈ KO k _) (p : ℕ) (T : n → Prop)
    (h1 : ∀ l s, T s → p ≤ l.val + 1 → valuation k (g.val (.inr l) (.inl s)) < 1)
    (h2 : ∀ r i, lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r →
      valuation k (g.val r (.inr i) - (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i)) < 1) :
    ∃ u ∈ KOne k (n ⊕ Fin c), ∃ D : Matrix (Fin c) n k, IntM D ∧ (∀ l s, T s → D l s = 0) ∧
      ∀ a b, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) →
        (g * u * lowU D).val a b = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) a b := by sorry
