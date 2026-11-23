-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_finsum_psi_le
-- name    : GlobalTheory.CuspGL.finsum_psi_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:46.41668+00:00
-- url     : https://prove2.me/theorems/8cfc0fd6-eaa9-459a-a2fe-958b1b4e181d
-- title:
--   Cusp GL: finsum psi le
-- statement:
--   The Cusp GL construction uses the finsum psi le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumMobiusInverseCharpolyInvariantLe.lean#L10-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumMobiusInverseCharpolyInvariantLe.lean#L10-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEqFinsumPsiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLe
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

theorem GlobalTheory.CuspGL.finsum_psi_le (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V)
    (hg : ∀ x ∈ A, g x ∈ A) :
    ∑ᶠ W : {W : Submodule F V // W ≤ A ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2)
      = s (LinearMap.charpoly (g.restrict hg)) := by sorry
