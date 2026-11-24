-- Prove2me | Theorems.Thm_GlobalTheory_LocSplit_exists_sqrt
-- name    : GlobalTheory.LocSplit.exists_sqrt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:14:21.645028+00:00
-- url     : https://prove2.me/theorems/e2482b8b-28b5-445d-bf83-ed957b4ab824
-- title:
--   Loc Split: exists sqrt
-- statement:
--   The Loc Split construction uses the exists sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L86-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIrreducible.lean#L86-L140

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

theorem GlobalTheory.LocSplit.exists_sqrt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (h2 : Module.finrank F E = 2) (hs : sig ≠ AlgHom.id F E) :
    ∃ (α : 𝓞 E) (a : 𝓞 F), (α : E) ≠ 0 ∧ sig α = -α ∧ algebraMap (𝓞 F) (𝓞 E) a = α ^ 2 ∧
      ∀ y : E, ∃ u v : F, y = algebraMap F E u + algebraMap F E v * α := by sorry
