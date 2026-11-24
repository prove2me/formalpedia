-- Prove2me | Theorems.Thm_GlobalTheory_SepGenElt_exists_aeval_eq
-- name    : GlobalTheory.SepGenElt.exists_aeval_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:53:22.856494+00:00
-- url     : https://prove2.me/theorems/dcc7d38d-8a25-4bb4-9876-fcc4109d0115
-- title:
--   Sep Gen Elt: exists aeval eq
-- statement:
--   The Sep Gen Elt construction uses the exists aeval eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfMulLeftCharpolySeparable.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfMulLeftCharpolySeparable.lean#L8-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfMulLeftCharpolySeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SepGenElt

theorem GlobalTheory.SepGenElt.exists_aeval_eq : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A),
    (LinearMap.mulLeft E g).charpoly.Separable → ∀ x : A, ∃ p : E[X], aeval g p = x := by sorry
