-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_realEmb_mul_hermTrace_pos
-- name    : GroundTheory.Automorphic.realEmb_mul_hermTrace_pos
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:48.348706+00:00
-- url     : https://prove2.me/theorems/06186f66-6f27-4647-a907-495e6d47fc22
-- title:
--   Automorphic: real Emb mul herm Trace pos
-- statement:
--   The Automorphic construction uses the real Emb mul herm Trace pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L190-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L190-L214

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

theorem GroundTheory.Automorphic.realEmb_mul_hermTrace_pos {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {w : InfinitePlace K} (hw : w.IsReal) {x : ι → K ⊗[K] E} (hx : x ≠ 0) :
    0 < embedding_of_isReal hw (θ * hermTrace K H K x x) := by sorry
