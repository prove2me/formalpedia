-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldFlag_exists_unipotent
-- name    : GlobalTheory.RootEx.UnfoldFlag.exists_unipotent
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:47.662854+00:00
-- url     : https://prove2.me/theorems/495f2577-8929-404a-92e0-b521b6f4be08
-- title:
--   Unfold Flag: exists unipotent
-- statement:
--   The Unfold Flag construction uses the exists unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsUnipotent.lean#L49-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsUnipotent.lean#L49-L160

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldFlag
variable {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.RootEx.UnfoldFlag.exists_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (hc : 1 ≤ c) (ϖ : 𝒪[k]), (ϖ : k) ≠ 0 → ∀ Λ : Submodule 𝒪[k] (n ⊕ Fin c → k), (∀ i : Fin c, (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (Sum.inr i)) = Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)}) → (ϖ : k) • aux k n (⟨0, hc⟩ : Fin c) ∈ Λ → ∃ u ∈ N k n c 1, act u Λ = chainLat ϖ c (Λ.comap (inX k n c)) := by sorry
