-- Prove2me | Theorems.Thm_GlobalTheory_exists_isLatticeEmb
-- name    : GlobalTheory.exists_isLatticeEmb
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:19.778863+00:00
-- url     : https://prove2.me/theorems/553b041f-92cd-4f38-9235-036141af7771
-- title:
--   Global Theory: exists is Lattice Emb
-- statement:
--   The Global Theory construction uses the exists is Lattice Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/HermitianLattices/ExistsZsmulMemOfIsLattice.lean#L179-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/HermitianLattices/ExistsZsmulMemOfIsLattice.lean#L179-L204

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

theorem GlobalTheory.exists_isLatticeEmb [Module.Finite (𝓞 K) M] [Module.IsTorsionFree (𝓞 K) M]
    (hr : Module.finrank (𝓞 K) M = r) : ∃ φ : M →ₗ[𝓞 K] (Fin r → K), IsLatticeEmb φ := by sorry
