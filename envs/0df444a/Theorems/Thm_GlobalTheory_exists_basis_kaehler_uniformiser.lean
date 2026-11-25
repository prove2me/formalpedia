-- Prove2me | Theorems.Thm_GlobalTheory_exists_basis_kaehler_uniformiser
-- name    : GlobalTheory.exists_basis_kaehler_uniformiser
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:17.702897+00:00
-- url     : https://prove2.me/theorems/2ff4ba7d-fd5e-4fbb-bb85-8bf003df844e
-- title:
--   Global Theory: exists basis kaehler uniformiser
-- statement:
--   The Global Theory construction uses the exists basis kaehler uniformiser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L499-L536
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L499-L536

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

theorem GlobalTheory.exists_basis_kaehler_uniformiser {t : V} (ht : Irreducible t) :
    ∃ (m : ℕ) (z : Fin (m + 1) → V) (b : Basis (Fin (m + 1)) V Ω[V⁄K]),
      z 0 = t ∧ ∀ k, b k = D K V (z k) := by sorry
