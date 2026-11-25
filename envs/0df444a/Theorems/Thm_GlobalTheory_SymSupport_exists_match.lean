-- Prove2me | Theorems.Thm_GlobalTheory_SymSupport_exists_match
-- name    : GlobalTheory.SymSupport.exists_match
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:29.666395+00:00
-- url     : https://prove2.me/theorems/1378d77f-4a3e-4429-96dd-34b3cb62b09b
-- title:
--   Sym Support: exists match
-- statement:
--   The Sym Support construction uses the exists match property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainSupportOneOfPattern.lean#L134-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainSupportOneOfPattern.lean#L134-L158

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SymSupport.exists_match {a t Y : Type} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] [Fintype Y] [DecidableEq Y]
    (Q : TypeDatum k a) (μ : kˣ →* ℂˣ) (e : a ⊕ t ≃ Y) {G : GL Y k} (hG : G ∈ KO k Y) (Z : Matrix Y a k)
    (h : Q.Phi t μ (((G⁻¹).val * Z).submatrix e id) ≠ 0) :
    ∃ κ : GL Y k, (reGL e).symm κ ∈ Q.stepJ t ∧ ∀ r b, valuation k ((G * κ).val r (e (.inl b)) - Z r b) < 1 := by sorry
