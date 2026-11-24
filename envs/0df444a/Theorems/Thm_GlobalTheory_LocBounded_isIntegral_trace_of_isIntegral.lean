-- Prove2me | Theorems.Thm_GlobalTheory_LocBounded_isIntegral_trace_of_isIntegral
-- name    : GlobalTheory.LocBounded.isIntegral_trace_of_isIntegral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:12:26.364151+00:00
-- url     : https://prove2.me/theorems/1a937ce7-35ba-433b-82df-5a3ddc6313d1
-- title:
--   Loc Bounded: is Integral trace of is Integral
-- statement:
--   The Loc Bounded construction uses the is Integral trace of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedOfIsIntegral.lean#L26-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedOfIsIntegral.lean#L26-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LocBounded

theorem GlobalTheory.LocBounded.isIntegral_trace_of_isIntegral {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : IsIntegral R M) : IsIntegral R M.trace := by sorry
