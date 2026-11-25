-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_ker_resOne
-- name    : GlobalTheory.PDivGroup.ker_resOne
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:49:18.989208+00:00
-- url     : https://prove2.me/theorems/e6c74b3e-e4ed-5677-ae4a-dbaec3c1d935
-- title:
--   PDiv Group: ker res One
-- statement:
--   The PDiv Group construction uses the ker res One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivGroupMulPUnitFibreEqLevelOne.lean#L20-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivGroupMulPUnitFibreEqLevelOne.lean#L20-L67

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupMulPUnitFibreEqLevelOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra GlobalTheory.PDiv
open GlobalTheory
open GlobalTheory.PDivGroup
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
open scoped TensorProduct
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R)

theorem GlobalTheory.PDivGroup.ker_resOne (n : ℕ) :
    RingHom.ker (G.resOne n :
      G.A (n + 1) →ₐ[R] G.A 1) =
      _root_.GlobalTheory.PDiv.torsionIdeal R (G.A (n + 1)) p := by sorry
