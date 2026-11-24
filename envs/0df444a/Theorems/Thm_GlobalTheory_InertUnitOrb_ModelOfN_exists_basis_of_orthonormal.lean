-- Prove2me | Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_exists_basis_of_orthonormal
-- name    : GlobalTheory.InertUnitOrb.ModelOfN.exists_basis_of_orthonormal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:54:45.608802+00:00
-- url     : https://prove2.me/theorems/d3af8dd3-cb95-41d9-874b-2ab1c06e00dc
-- title:
--   Model Of N: exists basis of orthonormal
-- statement:
--   The Model Of N construction uses the exists basis of orthonormal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianModelOfNormNeZero.lean#L252-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianModelOfNormNeZero.lean#L252-L269

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.InertUnitOrb GlobalTheory.InertUnitOrb.ModelOfN

theorem GlobalTheory.InertUnitOrb.ModelOfN.exists_basis_of_orthonormal {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [FiniteDimensional K.E V]
    (h : V → V → K.E) (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z)
    (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z) {n : ℕ} (hn : Module.finrank K.E V = n)
    (v : Fin n → V) (hv : ∀ i j, h (v i) (v j) = if i = j then 1 else 0) :
    ∃ b : Module.Basis (Fin n) K.E V, ∀ i, b i = v i := by sorry
