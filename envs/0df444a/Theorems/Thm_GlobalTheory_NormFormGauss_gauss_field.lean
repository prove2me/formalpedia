-- Prove2me | Theorems.Thm_GlobalTheory_NormFormGauss_gauss_field
-- name    : GlobalTheory.NormFormGauss.gauss_field
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:36:33.941403+00:00
-- url     : https://prove2.me/theorems/7846dc24-3395-48a3-bd34-4b976fd414b3
-- title:
--   Norm Form Gauss: gauss field
-- statement:
--   The Norm Form Gauss construction uses the gauss field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumEqZeroAddUnits.lean#L128-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumEqZeroAddUnits.lean#L128-L166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.NormFormGauss

theorem GlobalTheory.NormFormGauss.gauss_field {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) (f : k → ℂ) (hadd : ∀ a b, f (a + b) = f a * f b) (h0 : f 0 = 1)
    (u : k) (hu : s u = u) (hfu : f u ≠ 1) :
    ∑ x : k, f (x * s x) = -(Real.sqrt (Fintype.card k) : ℂ) := by sorry
