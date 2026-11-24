-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_ipGL_charpoly_eq_finsum_mass
-- name    : GlobalTheory.CuspGL.ipGL_charpoly_eq_finsum_mass
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:30.388793+00:00
-- url     : https://prove2.me/theorems/bfb06f5f-a5dd-4946-80a9-750247fb1b73
-- title:
--   Cusp GL: ip GL charpoly eq finsum mass
-- statement:
--   The Cusp GL construction uses the ip GL charpoly eq finsum mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsUnitIffCharpolyCoeffZeroNe.lean#L11-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsUnitIffCharpolyCoeffZeroNe.lean#L11-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsUnitIffCharpolyCoeffZeroNe
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
open Polynomial

theorem GlobalTheory.CuspGL.ipGL_charpoly_eq_finsum_mass (F : Type) [Field F] [Finite F]
    (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (φ : Module.End F V → ℂ) (s : F[X] → ℂ) :
    _root_.GlobalTheory.CuspGL.ipGL φ (fun g => s (LinearMap.charpoly g)) =
      ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0},
        _root_.GlobalTheory.CuspGL.mass φ P * star (s P) := by sorry
