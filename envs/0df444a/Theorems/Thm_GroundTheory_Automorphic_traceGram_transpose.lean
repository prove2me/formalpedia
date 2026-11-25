-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_traceGram_transpose
-- name    : GroundTheory.Automorphic.traceGram_transpose
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:32.892339+00:00
-- url     : https://prove2.me/theorems/25593dfb-5e9b-4744-a231-a1f3e3882623
-- title:
--   Automorphic: trace Gram transpose
-- statement:
--   The Automorphic construction uses the trace Gram transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L185-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L185-L188

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
omit [NumberField K] [Fintype κ]

theorem GroundTheory.Automorphic.traceGram_transpose (hH : IsHermitianFor (conjHom K E) H) :
    (traceGram H b)ᵀ = traceGram H b := by sorry
