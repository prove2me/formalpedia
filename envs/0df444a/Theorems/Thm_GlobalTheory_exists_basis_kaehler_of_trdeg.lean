-- Prove2me | Theorems.Thm_GlobalTheory_exists_basis_kaehler_of_trdeg
-- name    : GlobalTheory.exists_basis_kaehler_of_trdeg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:38.768798+00:00
-- url     : https://prove2.me/theorems/d7f11e20-869c-4843-a579-71559b957969
-- title:
--   Global Theory: exists basis kaehler of trdeg
-- statement:
--   The Global Theory construction uses the exists basis kaehler of trdeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L549-L557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L549-L557

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K : Type*) {V : Type*} [Field K] [PerfectField K] [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Algebra K V] [Algebra.EssFiniteType K V]
  [Algebra.FormallySmooth K V]
variable (F : Type*) [Field F] [Algebra V F] [IsFractionRing V F] [Algebra K F]
  [IsScalarTower K V F]

theorem GlobalTheory.exists_basis_kaehler_of_trdeg {n : ℕ} (hn : Algebra.trdeg K F = n) {t : V}
    (ht : Irreducible t) :
    ∃ (h : 0 < n) (z : Fin n → V) (b : Basis (Fin n) V Ω[V⁄K]),
      z ⟨0, h⟩ = t ∧ ∀ k, b k = D K V (z k) := by sorry
