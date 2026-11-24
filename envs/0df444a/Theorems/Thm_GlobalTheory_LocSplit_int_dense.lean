-- Prove2me | Theorems.Thm_GlobalTheory_LocSplit_int_dense
-- name    : GlobalTheory.LocSplit.int_dense
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:14:21.632602+00:00
-- url     : https://prove2.me/theorems/f0fc641b-144a-4538-a68c-48f3185bfb5d
-- title:
--   Loc Split: int dense
-- statement:
--   The Loc Split construction uses the int dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L62-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L62-L84

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.S.Loc NumberField IsDedekindDomain ValuativeRel
open GlobalTheory GlobalTheory.LocSplit

theorem GlobalTheory.LocSplit.int_dense {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) (g : ℕ)
    (h1 : (g : R) ∈ w.asIdeal) (h2 : (g : R) ∉ w.asIdeal ^ 2)
    (h3 : ∀ x : R, ∃ m : ℤ, x - m ∈ w.asIdeal) (x : R) (n : ℕ) :
    ∃ m : ℤ, x - m ∈ w.asIdeal ^ n := by sorry
