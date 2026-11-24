-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_IterPattern_iter_iff
-- name    : GlobalTheory.SymChain.IterPattern.iter_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:14.005808+00:00
-- url     : https://prove2.me/theorems/6c6dce3c-e858-438b-833b-2395c8835723
-- title:
--   Iter Pattern: iter iff
-- statement:
--   The Iter Pattern construction uses the iter iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainPatternIterated.lean#L105-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainPatternIterated.lean#L105-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPatternStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.IterPattern
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ρ κ l j : ℕ} {t : Type}
variable [Fintype t] [DecidableEq t]

theorem GlobalTheory.SymChain.IterPattern.iter_iff (P : TypeDatum k (Fin κ ⊕ Fin l)) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hP : ∀ g : GL (Fin κ ⊕ Fin l) k, g ∈ P.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (j : ℕ) (g : GL (Ix (Fin κ ⊕ Fin l) t j) k) :
    g ∈ (P.iter t μ hμ j).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by sorry
