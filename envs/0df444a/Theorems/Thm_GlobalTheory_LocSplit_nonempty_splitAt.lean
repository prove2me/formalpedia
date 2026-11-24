-- Prove2me | Theorems.Thm_GlobalTheory_LocSplit_nonempty_splitAt
-- name    : GlobalTheory.LocSplit.nonempty_splitAt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:27.689224+00:00
-- url     : https://prove2.me/theorems/6f8190a4-92b0-452d-8c09-404605d044b0
-- title:
--   Loc Split: nonempty split At
-- statement:
--   The Loc Split construction uses the nonempty split At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L280-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L280-L345

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

theorem GlobalTheory.LocSplit.nonempty_splitAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (sig : E →ₐ[F] E), Module.finrank F E = 2 → sig ≠ AlgHom.id F E →
    ∀ (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p),
    ((Ideal.span {(resChar p : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E →
    Nonempty (SplitAt L.Fp L.Ep L.cj (resChar p)) := by sorry
