-- Prove2me | Theorems.Thm_GlobalTheory_T_isSelfDual_image_standardLattice_unitary
-- name    : GlobalTheory.T.isSelfDual_image_standardLattice_unitary
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:50:53.675702+00:00
-- url     : https://prove2.me/theorems/cd85f18b-56fa-463f-865b-c00cd692232a
-- title:
--   T: is Self Dual image standard Lattice unitary
-- statement:
--   The T construction uses the is Self Dual image standard Lattice unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSelfDualImageStandardLatticeUnitaryStatement.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSelfDualImageStandardLatticeUnitaryStatement.lean#L8-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSelfDualImageStandardLatticeUnitary
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSelfDualImageStandardLatticeUnitaryStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isSelfDual_image_standardLattice_unitary : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) K), (g.map σ)ᵀ * g = 1 →
    SelfDual O σ (matLat O g (stdLat O n)) := by sorry
