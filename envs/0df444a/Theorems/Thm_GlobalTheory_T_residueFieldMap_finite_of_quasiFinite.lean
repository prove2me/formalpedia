-- Prove2me | Theorems.Thm_GlobalTheory_T_residueFieldMap_finite_of_quasiFinite
-- name    : GlobalTheory.T.residueFieldMap_finite_of_quasiFinite
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:04.947195+00:00
-- url     : https://prove2.me/theorems/a2b5aab2-993e-59ec-a22c-6f1e40c5e193
-- title:
--   T: residue Field Map finite of quasi Finite
-- statement:
--   The T construction uses the residue Field Map finite of quasi Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ResidueFieldMapFiniteOfQuasiFiniteStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ResidueFieldMapFiniteOfQuasiFiniteStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldMapFiniteOfQuasiFinite
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldMapFiniteOfQuasiFiniteStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.residueFieldMap_finite_of_quasiFinite : ∀ {Y Z : Scheme.{0}} (g : Y ⟶ Z) [LocallyQuasiFinite g] (y : Y), (g.residueFieldMap y).hom.Finite := by sorry
