-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hermTrace_eq_sum_traceGram
-- name    : GroundTheory.Automorphic.hermTrace_eq_sum_traceGram
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:04.136173+00:00
-- url     : https://prove2.me/theorems/c9d03d3f-7af3-48aa-91ce-012cd0ab82be
-- title:
--   Automorphic: herm Trace eq sum trace Gram
-- statement:
--   The Automorphic construction uses the herm Trace eq sum trace Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L110-L113

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
omit [NumberField K]

theorem GroundTheory.Automorphic.hermTrace_eq_sum_traceGram (x y : ι → R ⊗[K] E) :
    hermTrace K H R x y = ∑ a : ι × κ, ∑ c : ι × κ, vecCoords R b x a * vecCoords R b y c *
      algebraMap K R (traceGram H b a c) := by sorry
