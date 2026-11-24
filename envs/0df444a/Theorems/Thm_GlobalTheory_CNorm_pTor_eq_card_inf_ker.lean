-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_pTor_eq_card_inf_ker
-- name    : GlobalTheory.CNorm.pTor_eq_card_inf_ker
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:51.763887+00:00
-- url     : https://prove2.me/theorems/39d7d417-2673-43cf-bd46-bcc3f621afeb
-- title:
--   CNorm: p Tor eq card inf ker
-- statement:
--   The CNorm construction uses the p Tor eq card inf ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/PowIndexTorsionKerRangeMul.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/PowIndexTorsionKerRangeMul.lean#L9-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm

theorem GlobalTheory.CNorm.pTor_eq_card_inf_ker (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    pTor p U = Nat.card (U ⊓ (powMonoidHom p : G →* G).ker : Subgroup G) := by sorry
