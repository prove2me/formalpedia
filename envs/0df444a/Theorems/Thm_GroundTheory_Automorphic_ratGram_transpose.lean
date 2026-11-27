-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ratGram_transpose
-- name    : GroundTheory.Automorphic.ratGram_transpose
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:58:46.81702+00:00
-- url     : https://prove2.me/theorems/f1e53028-3e33-4250-9c62-0cf64902a8d3
-- title:
--   Automorphic: rat Gram transpose
-- statement:
--   The Automorphic construction uses the rat Gram transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L235-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L235-L242

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R]
variable {H b}
omit [Fintype κ]

theorem GroundTheory.Automorphic.ratGram_transpose (hH : IsHermitianFor (conjHom K E) H) (θ : K) :
    (ratGram H b θ)ᵀ = ratGram H b θ := by sorry
