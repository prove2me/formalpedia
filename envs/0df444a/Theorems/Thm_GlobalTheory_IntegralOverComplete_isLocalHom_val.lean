-- Prove2me | Theorems.Thm_GlobalTheory_IntegralOverComplete_isLocalHom_val
-- name    : GlobalTheory.IntegralOverComplete.isLocalHom_val
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:20:36.745577+00:00
-- url     : https://prove2.me/theorems/aff320fd-22c1-4c96-a2da-e0d212eee707
-- title:
--   Integral Over Complete: is Local Hom val
-- statement:
--   The Integral Over Complete construction uses the is Local Hom val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HenselianIUnionCompleteOfIntegralOverCompleteDvr.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HenselianIUnionCompleteOfIntegralOverCompleteDvr.lean#L10-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HenselianIUnionCompleteOfIntegralOverCompleteDvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.IntegralOverComplete
open IsLocalRing Polynomial

theorem GlobalTheory.IntegralOverComplete.isLocalHom_val {W R : Type} [CommRing W] [CommRing R] [Algebra W R]
    [Algebra.IsIntegral W R] (W' : Subalgebra W R) : IsLocalHom W'.val.toRingHom := by sorry
