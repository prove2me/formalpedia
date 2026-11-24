-- Prove2me | Theorems.Thm_GlobalTheory_IsLatticeEmb_comp_GL
-- name    : GlobalTheory.IsLatticeEmb.comp_GL
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:52:21.876617+00:00
-- url     : https://prove2.me/theorems/46389a12-562b-48df-ae71-0e91aa2caf30
-- title:
--   Is Lattice Emb: comp GL
-- statement:
--   The Is Lattice Emb construction uses the comp GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/HermitianLattices/ExistsZsmulMemOfIsLattice.lean#L126-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/HermitianLattices/ExistsZsmulMemOfIsLattice.lean#L126-L133

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
open GlobalTheory.IsLatticeEmb
variable {φ : M →ₗ[𝓞 K] (Fin r → K)}

theorem GlobalTheory.IsLatticeEmb.comp_GL (h : IsLatticeEmb φ) (γ : GL (Fin r) K) :
    IsLatticeEmb (((γ : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars (𝓞 K)) ∘ₗ φ) := by sorry
