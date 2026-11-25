-- Prove2me | Theorems.Thm_GlobalTheory_FlagDomain_gram_eq_transpose_mul
-- name    : GlobalTheory.FlagDomain.gram_eq_transpose_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:42:12.545351+00:00
-- url     : https://prove2.me/theorems/4465d9a5-d4ff-5694-a9ca-c27282b725fe
-- title:
--   Flag Domain: gram eq transpose mul
-- statement:
--   The Flag Domain construction uses the gram eq transpose mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DefiniteFrameLeadingMinorsSign.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DefiniteFrameLeadingMinorsSign.lean#L9-L15

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DefiniteFrameLeadingMinorsSign
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexOrder ComplexConjugate Matrix
open GlobalTheory GlobalTheory.FlagDomain

theorem GlobalTheory.FlagDomain.gram_eq_transpose_mul {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by sorry
