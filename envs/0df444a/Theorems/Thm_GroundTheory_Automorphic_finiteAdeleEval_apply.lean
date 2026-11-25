-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_finiteAdeleEval_apply
-- name    : GroundTheory.Automorphic.finiteAdeleEval_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:48.628814+00:00
-- url     : https://prove2.me/theorems/b62322dd-0d3c-4145-b7d5-ade06877453d
-- title:
--   Automorphic: finite Adele Eval apply
-- statement:
--   The Automorphic construction uses the finite Adele Eval apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Restricted.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Restricted.lean#L29-L30

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Lattice
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Restricted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct Topology Filter IsDedekindDomain NumberField
open scoped RestrictedProduct
noncomputable section
variable {K E : Type*} [Field K] [NumberField K] [CommRing E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

theorem GroundTheory.Automorphic.finiteAdeleEval_apply (v : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 K) K) :
    finiteAdeleEval K v a = a v := by sorry
