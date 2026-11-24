-- Prove2me | Theorems.Thm_GlobalTheory_CoprimeBasisExistence_exists_basis_coprime
-- name    : GlobalTheory.CoprimeBasisExistence.exists_basis_coprime
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:54:53.104907+00:00
-- url     : https://prove2.me/theorems/9fcc30bb-2132-431a-a53b-887cf94e409e
-- title:
--   Coprime Basis Existence: exists basis coprime
-- statement:
--   The Coprime Basis Existence construction uses the exists basis coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsPrincipalIdealRingLoc.lean#L78-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IsPrincipalIdealRingLoc.lean#L78-L160

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsPrincipalIdealRingLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoprimeBasisExistence
open NumberField nonZeroDivisors

theorem GlobalTheory.CoprimeBasisExistence.exists_basis_coprime {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (m : ℕ) (hm : 0 < m)
    (L : Submodule (𝓞 K) V) (hL : L.FG) :
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, ∃ k : ℕ, Nat.Coprime k m ∧ k • w ∈ Submodule.span (𝓞 K) (Set.range b) := by sorry
