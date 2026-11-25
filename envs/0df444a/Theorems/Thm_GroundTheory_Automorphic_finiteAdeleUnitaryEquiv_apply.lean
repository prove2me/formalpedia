-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
-- name    : GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:48:52.973025+00:00
-- url     : https://prove2.me/theorems/a042c013-043a-4aa2-bdef-aaf799be2df0
-- title:
--   Automorphic: finite Adele Unitary Equiv apply
-- statement:
--   The Automorphic construction uses the finite Adele Unitary Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Restricted.lean#L223-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Restricted.lean#L223-L225

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

theorem GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply (hH : IsUnit H.det)
    (g : unitaryPoints K E H (FiniteAdeleRing (𝓞 K) K)) (v : HeightOneSpectrum (𝓞 K)) :
    finiteAdeleUnitaryEquiv H b hH g v = unitaryMap K E H (finiteAdeleEval K v) g := by sorry

attribute [defeq] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
