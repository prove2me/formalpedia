-- Prove2me | Theorems.Thm_GlobalTheory_residueFieldMap_finite_of_locallyQuasiFinite
-- name    : GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:16:19.765362+00:00
-- url     : https://prove2.me/theorems/2bf93032-b87d-4458-b4c3-9d7e5dcc53ea
-- title:
--   Global Theory: residue Field Map finite of locally Quasi Finite
-- statement:
--   The Global Theory construction uses the residue Field Map finite of locally Quasi Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ResidueFieldMapFiniteOfQuasiFinite.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ResidueFieldMapFiniteOfQuasiFinite.lean#L26-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldMapFiniteOfQuasiFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory

theorem GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite {Y Z : Scheme.{0}} (g : Y ⟶ Z)
    [LocallyQuasiFinite g] (y : Y) : (g.residueFieldMap y).hom.Finite := by sorry
