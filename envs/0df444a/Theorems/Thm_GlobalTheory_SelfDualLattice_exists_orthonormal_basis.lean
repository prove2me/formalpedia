-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualLattice_exists_orthonormal_basis
-- name    : GlobalTheory.SelfDualLattice.exists_orthonormal_basis
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:52:39.810663+00:00
-- url     : https://prove2.me/theorems/c9cc5048-864f-4bc5-9f36-c636743e19d2
-- title:
--   Self Dual Lattice: exists orthonormal basis
-- statement:
--   The Self Dual Lattice construction uses the exists orthonormal basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelfDualHermitianLatticeBasisExists.lean#L58-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelfDualHermitianLatticeBasisExists.lean#L58-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualHermitianLatticeBasisExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.SelfDualLattice

theorem GlobalTheory.SelfDualLattice.exists_orthonormal_basis : ∀ (K : UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [Module.Finite K.E V] (h : V → V → K.E),
    (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) →
    (∀ x y, h y x = K.c (h x y)) → ∀ L : Submodule K.O V, L.FG →
    Submodule.span K.E (L : Set V) = ⊤ →
    (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V, Submodule.span K.O (Set.range b) = L ∧
      ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by sorry
