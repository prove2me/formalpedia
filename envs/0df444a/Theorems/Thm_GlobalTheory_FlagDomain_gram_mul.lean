-- Prove2me | Theorems.Thm_GlobalTheory_FlagDomain_gram_mul
-- name    : GlobalTheory.FlagDomain.gram_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:42:35.123954+00:00
-- url     : https://prove2.me/theorems/362af77c-a6a6-4592-a4ac-abd4bf1155d8
-- title:
--   Flag Domain: gram mul
-- statement:
--   The Flag Domain construction uses the gram mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DefiniteFrameLeadingMinorsSign.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DefiniteFrameLeadingMinorsSign.lean#L17-L22

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

theorem GlobalTheory.FlagDomain.gram_mul {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (P * Q) = Qᵀ * gram τ G P * Q.map (starRingEnd ℂ) := by sorry
