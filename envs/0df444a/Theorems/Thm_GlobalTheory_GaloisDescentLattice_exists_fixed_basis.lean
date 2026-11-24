-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescentLattice_exists_fixed_basis
-- name    : GlobalTheory.GaloisDescentLattice.exists_fixed_basis
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:35:06.526803+00:00
-- url     : https://prove2.me/theorems/236822d2-b6ea-4975-8b1e-b9eda8a90187
-- title:
--   Galois Descent Lattice: exists fixed basis
-- statement:
--   The Galois Descent Lattice construction uses the exists fixed basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFixedBasis.lean#L15-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFixedBasis.lean#L15-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixedBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
open GlobalTheory GlobalTheory.GaloisDescentLattice

theorem GlobalTheory.GaloisDescentLattice.exists_fixed_basis : ∀ (K : UQ) (B : InvAlg K) (M : Submodule K.O B.A), IsLat K.O K.E M →
    (∀ y ∈ M, B.σ y ∈ M) → ∃ e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A,
      Submodule.span K.O (Set.range e) = M ∧ ∀ i, B.σ (e i) = e i := by sorry
