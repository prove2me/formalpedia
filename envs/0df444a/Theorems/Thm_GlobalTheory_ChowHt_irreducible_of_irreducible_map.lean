-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_irreducible_of_irreducible_map
-- name    : GlobalTheory.ChowHt.irreducible_of_irreducible_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:14:46.203679+00:00
-- url     : https://prove2.me/theorems/f39cf5e5-7bc0-499a-a954-285ef5c61df7
-- title:
--   Chow Ht: irreducible of irreducible map
-- statement:
--   The Chow Ht construction uses the irreducible of irreducible map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L41-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IrreducibleOfIrreducibleMap.lean#L41-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type} [Field k] {N : ℕ}

theorem GlobalTheory.ChowHt.irreducible_of_irreducible_map {K σ : Type} [Field K] [Algebra k K] {f : MvPolynomial σ k}
    (h : Irreducible (MvPolynomial.map (algebraMap k K) f)) : Irreducible f := by sorry
