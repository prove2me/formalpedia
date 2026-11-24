-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrincipalCongruence_exists_principalCongruence
-- name    : GlobalTheory.CompanionTheory.PrincipalCongruence.exists_principalCongruence
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:09:56.871438+00:00
-- url     : https://prove2.me/theorems/86fe63da-5f14-4a70-bb8a-f0939c2b7b5a
-- title:
--   Principal Congruence: exists principal Congruence
-- statement:
--   The Principal Congruence construction uses the exists principal Congruence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsPrincipalCongruence.lean#L101-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsPrincipalCongruence.lean#L101-L109

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrincipalCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrincipalCongruence
variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem GlobalTheory.CompanionTheory.PrincipalCongruence.exists_principalCongruence :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (t : k), t ≠ 0 → ValuativeRel.valuation k (t) < 1 →
      ∃ H : Subgroup (GL (Fin N) k), (H : Set (GL (Fin N) k)) =
        {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
          ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
            ValuativeRel.valuation k (t)} := by sorry
