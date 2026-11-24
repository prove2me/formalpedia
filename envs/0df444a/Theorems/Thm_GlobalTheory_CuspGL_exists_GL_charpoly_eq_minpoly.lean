-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_exists_GL_charpoly_eq_minpoly
-- name    : GlobalTheory.CuspGL.exists_GL_charpoly_eq_minpoly
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:30:55.29961+00:00
-- url     : https://prove2.me/theorems/cd21485a-c2e7-472b-a5d1-6d4810105366
-- title:
--   Cusp GL: exists GL charpoly eq minpoly
-- statement:
--   The Cusp GL construction uses the exists GL charpoly eq minpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RegularIffNatDegreeAndExistsEllipticGL.lean#L39-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RegularIffNatDegreeAndExistsEllipticGL.lean#L39-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.exists_GL_charpoly_eq_minpoly (F K : Type) [Field F] [Field K] [Algebra F K]
    (α : K) (hx : IsIntegral F α) (h0 : α ≠ 0) (n : ℕ) (hn : (minpoly F α).natDegree = n) :
    ∃ x : GL (Fin n) F, Matrix.charpoly (x : Matrix (Fin n) (Fin n) F) = minpoly F α := by sorry
