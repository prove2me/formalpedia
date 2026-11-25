-- Prove2me | Theorems.Thm_GlobalTheory_exists_linearIndependent_sumElim_of_finrank_eq
-- name    : GlobalTheory.exists_linearIndependent_sumElim_of_finrank_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:52.171437+00:00
-- url     : https://prove2.me/theorems/7aa86256-e17b-49de-80d8-9c0882bb14fe
-- title:
--   Global Theory: exists linear Independent sum Elim of finrank eq
-- statement:
--   The Global Theory construction uses the exists linear Independent sum Elim of finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsLinearIndependentSumElimOfFinrankEq.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsLinearIndependentSumElimOfFinrankEq.lean#L7-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsLinearIndependentSumElimOfFinrankEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory

theorem GlobalTheory.exists_linearIndependent_sumElim_of_finrank_eq {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] {n₀ n' : ℕ} (hV : Module.finrank k V = n₀ + n')
    (v : Fin n₀ → V) (hv : LinearIndependent k v) :
    ∃ w : Fin n' → V, LinearIndependent k (Sum.elim v w) := by sorry
