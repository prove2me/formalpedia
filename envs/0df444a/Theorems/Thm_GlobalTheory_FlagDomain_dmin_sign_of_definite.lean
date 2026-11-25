-- Prove2me | Theorems.Thm_GlobalTheory_FlagDomain_dmin_sign_of_definite
-- name    : GlobalTheory.FlagDomain.dmin_sign_of_definite
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:42:18.028356+00:00
-- url     : https://prove2.me/theorems/6211d010-ca8a-4edd-99e5-331ce6e44ab4
-- title:
--   Flag Domain: dmin sign of definite
-- statement:
--   The Flag Domain construction uses the dmin sign of definite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DefiniteFrameLeadingMinorsSign.lean#L24-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DefiniteFrameLeadingMinorsSign.lean#L24-L76

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

theorem GlobalTheory.FlagDomain.dmin_sign_of_definite (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (h : X.p0 = 0 ∨ X.p0 = r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (hx : (mat x τ).det ≠ 0) (i : Fin (r + 1)) :
    0 < psgn X.p0 i * (dmin X.Gm x τ i).re := by sorry
