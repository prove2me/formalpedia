-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticEtale_trace_surjective
-- name    : GlobalTheory.QuadraticEtale.trace_surjective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:12:49.782541+00:00
-- url     : https://prove2.me/theorems/fe512cc2-7030-4ec0-8918-dfbac88834bd
-- title:
--   Quadratic Etale: trace surjective
-- statement:
--   The Quadratic Etale construction uses the trace surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean#L390-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean#L390-L401

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
open Module
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
  [Module.Free R S] [Algebra.FormallyUnramified R S]

theorem GlobalTheory.QuadraticEtale.trace_surjective (hrank : finrank R S = 2) :
    Function.Surjective (Algebra.trace R S) := by sorry
