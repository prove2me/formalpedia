-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_exists_split_unif_idele
-- name    : GlobalTheory.CMVal.Euler.exists_split_unif_idele
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:04:38.567797+00:00
-- url     : https://prove2.me/theorems/0ff80b3c-b856-4341-9474-1e6fc7c3e95e
-- title:
--   Euler: exists split unif idele
-- statement:
--   The Euler construction uses the exists split unif idele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSplitPlaceUniformiserIdele.lean#L13-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSplitPlaceUniformiserIdele.lean#L13-L54

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSplitPlaceUniformiserIdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler

theorem GlobalTheory.CMVal.Euler.exists_split_unif_idele : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)) (x : OF E),
    Splits v → (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) →
    ∃ π : (Af E)ˣ, (∀ P, Over P v → (π : Af E) P = iota x P) ∧ (∀ P, ¬ Over P v → (π : Af E) P = 1) ∧
      modF π = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ 2 ∧ ∀ χ : HChar E, TrivOnF χ → finPart χ π = 1 := by sorry
