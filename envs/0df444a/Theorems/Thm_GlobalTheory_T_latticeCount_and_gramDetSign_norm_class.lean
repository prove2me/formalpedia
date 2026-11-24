-- Prove2me | Theorems.Thm_GlobalTheory_T_latticeCount_and_gramDetSign_norm_class
-- name    : GlobalTheory.T.latticeCount_and_gramDetSign_norm_class
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:24.25136+00:00
-- url     : https://prove2.me/theorems/fc7b28d9-2f51-491f-9b02-3fb13705737b
-- title:
--   T: lattice Count and gram Det Sign norm class
-- statement:
--   The T construction uses the lattice Count and gram Det Sign norm class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountAndGramDetSignNormClassStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountAndGramDetSignNormClassStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountAndGramDetSignNormClass
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountAndGramDetSignNormClassStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.latticeCount_and_gramDetSign_norm_class : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (u : B.Aˣ), B.N (x * (u * B.σ (u : B.A))) = B.N x ∧ K.eta (B.gramDet (x * (u * B.σ (u : B.A)))) = K.eta (B.gramDet x) := by sorry
