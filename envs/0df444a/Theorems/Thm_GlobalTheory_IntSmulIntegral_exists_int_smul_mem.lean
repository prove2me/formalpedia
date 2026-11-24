-- Prove2me | Theorems.Thm_GlobalTheory_IntSmulIntegral_exists_int_smul_mem
-- name    : GlobalTheory.IntSmulIntegral.exists_int_smul_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:18.705141+00:00
-- url     : https://prove2.me/theorems/f561ef97-fee4-4d68-97e0-87df1ac75dd6
-- title:
--   Int Smul Integral: exists int smul mem
-- statement:
--   The Int Smul Integral construction uses the exists int smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/Imports.lean#L14-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/Imports.lean#L14-L36

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntSmulIntegral
open NumberField

theorem GlobalTheory.IntSmulIntegral.exists_int_smul_mem {r : ℕ} {K : Type} [Field K] [NumberField K]
    {Λ : Submodule (𝓞 K) (Fin r → K)} (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) (v : Fin r → K) :
    ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ Λ := by sorry
