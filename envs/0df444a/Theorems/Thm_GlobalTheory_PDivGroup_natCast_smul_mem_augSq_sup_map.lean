-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_natCast_smul_mem_augSq_sup_map
-- name    : GlobalTheory.PDivGroup.natCast_smul_mem_augSq_sup_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:50:08.880871+00:00
-- url     : https://prove2.me/theorems/918aa580-8970-5ede-a380-a4bd3a361a50
-- title:
--   PDiv Group: nat Cast smul mem aug Sq sup map
-- statement:
--   The PDiv Group construction uses the nat Cast smul mem aug Sq sup map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCastSmulMemAugIdealSqSupMapMulP.lean#L14-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCastSmulMemAugIdealSqSupMapMulP.lean#L14-L42

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCastSmulMemAugIdealSqSupMapMulP
import Theorems.Thm_GlobalTheory_IsBicharacter_map

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
open Coalgebra Bialgebra
open GlobalTheory
open PDiv

theorem GlobalTheory.PDivGroup.natCast_smul_mem_augSq_sup_map : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ),
    ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))),
      (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 ⊔
        (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map
          ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by sorry
