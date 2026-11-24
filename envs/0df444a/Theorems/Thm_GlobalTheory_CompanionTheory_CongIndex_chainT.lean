-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_chainT
-- name    : GlobalTheory.CompanionTheory.CongIndex.chainT
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:25.584491+00:00
-- url     : https://prove2.me/theorems/9a204708-2dd0-4bd3-bebd-ba162dde9e4f
-- title:
--   Cong Index: chain T
-- statement:
--   The Cong Index construction uses the chain T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L237-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L237-L271

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CongIndex
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {N : ℕ}

theorem GlobalTheory.CompanionTheory.CongIndex.chainT {ϖ : k} (h0 : ϖ ≠ 0) (h1 : valuation k ϖ < 1)
    (hu : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ)
    {m : ℕ} (hm : 1 ≤ m) {b : Fin N → Fin N → ℕ} (hb : ∀ i j l, b i j ≤ b i l + b l j)
    (hb0 : ∀ i, b i i = 0)
    (H : Subgroup (GL (Fin N) k)) (hH : (H : Set (GL (Fin N) k)) = Kset ϖ (fun _ _ => m)) (t : ℕ) :
    ∃ G : Subgroup (GL (Fin N) k),
      (G : Set (GL (Fin N) k)) = Kset ϖ (fun i j => m + min (b i j) t) ∧ G ≤ H ∧
      G.relIndex H = Nat.card (IsLocalRing.ResidueField (valuation k).integer) ^
        (∑ i, ∑ j, min (b i j) t) := by sorry
