-- Prove2me | Theorems.Thm_GlobalTheory_LocSplit_val_eq_of
-- name    : GlobalTheory.LocSplit.val_eq_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:35.03641+00:00
-- url     : https://prove2.me/theorems/b79ca113-a0a2-4caa-ab05-672248e2ac81
-- title:
--   Loc Split: val eq of
-- statement:
--   The Loc Split construction uses the val eq of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L7-L16

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

theorem GlobalTheory.LocSplit.val_eq_of {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) (g : R)
    (h1 : g ∈ w.asIdeal) (h2 : g ∉ w.asIdeal ^ 2) : w.intValuation g = WithZero.exp (-1 : ℤ) := by sorry
