-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_linearIndependent_realEmb_integralBasis
-- name    : GroundTheory.Automorphic.linearIndependent_realEmb_integralBasis
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:37:18.41984+00:00
-- url     : https://prove2.me/theorems/48a52ac0-24c5-4a2d-bcf7-d195b687b1f1
-- title:
--   Automorphic: linear Independent real Emb integral Basis
-- statement:
--   The Automorphic construction uses the linear Independent real Emb integral Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L244-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L244-L265

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

theorem GroundTheory.Automorphic.linearIndependent_realEmb_integralBasis (hreal : ∀ w : InfinitePlace K, w.IsReal) :
    LinearIndependent ℝ fun t : Free.ChooseBasisIndex ℤ (𝓞 K) =>
      fun w : {w : InfinitePlace K // w.IsReal} => embedding_of_isReal w.2 (integralBasis K t) := by sorry
