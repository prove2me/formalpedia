-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_chainS
-- name    : GlobalTheory.CompanionTheory.CongIndex.chainS
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:26.318475+00:00
-- url     : https://prove2.me/theorems/aaa5cb74-4f6a-4189-8013-51b175873a9d
-- title:
--   Cong Index: chain S
-- statement:
--   The Cong Index construction uses the chain S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L207-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ValZpowIff.lean#L207-L235

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

theorem GlobalTheory.CompanionTheory.CongIndex.chainS {ϖ : k} (h0 : ϖ ≠ 0) (h1 : valuation k ϖ < 1)
    (hu : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ)
    {m : ℕ} (hm : 1 ≤ m) {b : Fin N → Fin N → ℕ} (hb : ∀ i j l, b i j ≤ b i l + b l j)
    (G : Subgroup (GL (Fin N) k)) (hG : (G : Set (GL (Fin N) k)) = Kset ϖ (fun i j => m + b i j))
    (S : Finset (Fin N × Fin N)) (hS : ∀ p ∈ S, p.1 ≠ p.2) :
    ∃ G' : Subgroup (GL (Fin N) k),
      (G' : Set (GL (Fin N) k)) = Kset ϖ (fun i j => m + b i j + if (i, j) ∈ S then 1 else 0) ∧
      G' ≤ G ∧
      G'.relIndex G = Nat.card (IsLocalRing.ResidueField (valuation k).integer) ^ S.card := by sorry
