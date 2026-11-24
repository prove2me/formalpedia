-- Prove2me | Theorems.Thm_GlobalTheory_isLatticeEmb_subtype
-- name    : GlobalTheory.isLatticeEmb_subtype
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:09.407911+00:00
-- url     : https://prove2.me/theorems/860957f8-37a4-4306-a4c7-0fc2d342bc59
-- title:
--   Global Theory: is Lattice Emb subtype
-- statement:
--   The Global Theory construction uses the is Lattice Emb subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/HermitianLattices/ExistsZsmulMemOfIsLattice.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/HermitianLattices/ExistsZsmulMemOfIsLattice.lean#L33-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open NumberField Matrix
open ReciprocityTheory.MultiplicativeHeights (IsLattice)
open scoped TensorProduct nonZeroDivisors
variable {r : ℕ}
variable {K : Type} [Field K] [NumberField K]
variable {M M' : Type} [AddCommGroup M] [Module (𝓞 K) M] [AddCommGroup M'] [Module (𝓞 K) M']

theorem GlobalTheory.isLatticeEmb_subtype {Λ : Submodule (𝓞 K) (Fin r → K)} (hΛ : IsLattice Λ) :
    IsLatticeEmb Λ.subtype := by sorry
