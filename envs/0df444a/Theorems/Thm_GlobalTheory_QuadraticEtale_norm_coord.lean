-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticEtale_norm_coord
-- name    : GlobalTheory.QuadraticEtale.norm_coord
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:19:44.722397+00:00
-- url     : https://prove2.me/theorems/e1db9115-6590-43ce-82ad-8e7119a7c633
-- title:
--   Quadratic Etale: norm coord
-- statement:
--   The Quadratic Etale construction uses the norm coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean#L171-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean#L171-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsUnitFormSelfOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.QuadraticEtale
open TensorProduct Module
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem GlobalTheory.QuadraticEtale.norm_coord (B : Basis (Fin 2) R S) (hB : B 0 = 1) {a b : R}
    (hab : B 1 * B 1 = algebraMap R S b + algebraMap R S a * B 1) (r s : R) :
    Algebra.norm R (algebraMap R S r + algebraMap R S s * B 1)
      = r * (r + s * a) - s * b * s := by sorry
