-- Prove2me | Theorems.Thm_GlobalTheory_LocSplit_split_prime
-- name    : GlobalTheory.LocSplit.split_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:57.769854+00:00
-- url     : https://prove2.me/theorems/8b36da1c-7e50-473d-ba27-2a394adce206
-- title:
--   Loc Split: split prime
-- statement:
--   The Loc Split construction uses the split prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L18-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L18-L60

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

theorem GlobalTheory.LocSplit.split_prime {E : Type} [Field E] [NumberField E] {g : ℕ} (hg : g.Prime)
    (h : (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hgP : (g : 𝓞 E) ∈ P) :
    (g : 𝓞 E) ∉ P ^ 2 ∧ ∀ x : 𝓞 E, ∃ m : ℤ, x - m ∈ P := by sorry
