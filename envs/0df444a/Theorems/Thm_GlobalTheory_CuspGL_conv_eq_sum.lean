-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_conv_eq_sum
-- name    : GlobalTheory.CuspGL.conv_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:09.59626+00:00
-- url     : https://prove2.me/theorems/63005fdf-d3df-4e03-a842-dc8c53da3040
-- title:
--   Cusp GL: conv eq sum
-- statement:
--   The Cusp GL construction uses the conv eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MonicFactorizationConvolutionFiniteCommAssocAdd.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MonicFactorizationConvolutionFiniteCommAssocAdd.lean#L25-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]

theorem GlobalTheory.CuspGL.conv_eq_sum (a b : F[X] → ℂ) (P : F[X]) :
    conv a b P = ∑ x ∈ (finite_monic_factorisations P).toFinset, a x.1 * b x.2 := by sorry
