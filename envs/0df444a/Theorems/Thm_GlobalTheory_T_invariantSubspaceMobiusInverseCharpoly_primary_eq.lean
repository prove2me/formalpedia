-- Prove2me | Theorems.Thm_GlobalTheory_T_invariantSubspaceMobiusInverseCharpoly_primary_eq
-- name    : GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_primary_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:47:57.140018+00:00
-- url     : https://prove2.me/theorems/93ce5bf7-180a-43cc-8c54-2aeafa7a42cd
-- title:
--   T: invariant Subspace Mobius Inverse Charpoly primary eq
-- statement:
--   The T construction uses the invariant Subspace Mobius Inverse Charpoly primary eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantSubspaceMobiusInverseCharpolyPrimaryEqStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantSubspaceMobiusInverseCharpolyPrimaryEqStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantSubspaceMobiusInverseCharpolyPrimaryEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantSubspaceMobiusInverseCharpolyPrimaryEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_primary_eq : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ (g : Module.End F V) (f : F[X]) (m t : ℕ), f.Monic → Irreducible f → 0 < m → LinearMap.charpoly g = f ^ m → Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t → psi s V g = s f * ∏ i ∈ Finset.Ico 1 t, (1 - (Nat.card F : ℂ) ^ (f.natDegree * i)) := by sorry
